import Goose.Evidence.Typing
import Goose.Evidence.TypingValidation

namespace Goose.Evidence

open Goose.Core Goose.GIR

namespace AggregateReferences

private def initializer : Func :=
  { name := "unit-global"
    params := []
    results := [.unit]
    slots := #[]
    scopes := #[]
    blocks := #[⟨[], [.def 0 .constUnit, .term (.ret [0] none)]⟩]
    summary := .unknown
    org := none }

private def entry : Func :=
  { name := "reference-array"
    params := []
    results := []
    slots := #[]
    scopes := #[]
    blocks := #[⟨[], [.def 0 (.globalAddr 0),
      .def 1 (.arrLit (.arr (.ref .readOnly .unit) 1) [0]), .term (.ret [] none)]⟩]
    summary := .unknown
    org := none }

private def module : GIR.Module :=
  { files := #["reference-array"]
    globals := #[⟨"unit", .unit, .immutable, initializer, 0⟩]
    funcs := #[entry]
    entry := 0
    origins := #[⟨0, 1, "global"⟩] }

#guard match validate module with | .ok () => true | .error _ => false
#guard match run 20 .release module with | .done .returned "" => true | _ => false
#guard (entry.valueTypes module)[1]? == some (some (.data (.arr (.ref .readOnly .unit) 1)))

private theorem referenceArrayTyped :
    WeakValueTy (runtimeDeclarations ⟨.release, module⟩ (fun _ => none))
      (.fixed #[.ref ⟨.global 0, []⟩]) (.arr (.ref .readOnly .unit) 1) := by
  refine ⟨rfl, ?_⟩
  intro index selected present
  simp only [Array.getElem?_singleton] at present
  split at present
  · cases present
    refine ⟨_, rfl, .unit, ?_, .root .unit⟩
    simp [runtimeDeclarations, module]
  · contradiction

end AggregateReferences

theorem enterBranch_typed {cfg : GCfg} {activations : ActivationTypes} {fn : Func}
    {fr fr' : Frame} {before readState after : St} {target : BlockId} {dest : GIR.Block}
    {args : List ValueId} {values : List RVal}
    (accepted : validate cfg.mod = .ok ()) (member : fn ∈ cfg.mod.allFuncs)
    (frameTyped : RuntimeFrameTy cfg fn activations fr before)
    (lookup : fn.blocks[target]? = some dest)
    (argMetadata : args.map (fun id => (fn.valueTypes cfg.mod)[id]?) =
      dest.params.map (fun param => some (some param.2)))
    (read : mapList (getCell fr) args before = .ok values readState)
    (entered : enterBlock fn fr target values readState = .ok (instsAt fn (target, 0), fr') after) :
    RuntimeFrameTy cfg fn activations fr' after := by
  obtain ⟨argsTyped, sameReadState⟩ := frameTyped.2.2.branchArgs argMetadata read
  subst readState
  obtain ⟨afterTyped, sameState⟩ := enterBlock_typed lookup frameTyped.2.2
    (fun param present => validated_block_param_metadata accepted member
      (Array.mem_of_getElem? lookup) present) argsTyped entered
  have sameAct := enterBlock_act entered
  refine ⟨sameState ▸ frameTyped.1, ?_, afterTyped⟩
  rw [sameAct]
  exact frameTyped.2.1

theorem RuntimeStep.branch_typed {cfg : GCfg} {activations : ActivationTypes} {fn : Func}
    {point : Pt} {fr fr' : Frame} {before readState after : St} {target : BlockId}
    {args : List ValueId} {values : List RVal}
    (accepted : validate cfg.mod = .ok ()) (member : fn ∈ cfg.mod.allFuncs)
    (frameTyped : RuntimeFrameTy cfg fn activations fr before)
    (instruction : instAt fn point = some (.term (.br target args)))
    (read : mapList (getCell fr) args before = .ok values readState)
    (entered : enterBlock fn fr target values readState = .ok (instsAt fn (target, 0), fr') after) :
    RuntimeFrameTy cfg fn activations fr' after := by
  obtain ⟨sourceValid, lastTerm⟩ := validated_instAt_term_last accepted member instruction
  obtain ⟨dest, lookup, argMetadata⟩ := validated_branch_metadata accepted member sourceValid lastTerm
  exact enterBranch_typed accepted member frameTyped lookup argMetadata read entered

theorem RuntimeStep.branchTrue_typed {cfg : GCfg} {activations : ActivationTypes} {fn : Func}
    {point : Pt} {fr fr' : Frame} {before tested readState after : St} {condition : ValueId}
    {target other : BlockId} {args otherArgs : List ValueId} {values : List RVal}
    (accepted : validate cfg.mod = .ok ()) (member : fn ∈ cfg.mod.allFuncs)
    (frameTyped : RuntimeFrameTy cfg fn activations fr before)
    (instruction : instAt fn point = some (.term (.condbr condition target args other otherArgs)))
    (test : (getVal fr condition >>= expectBool) before = .ok true tested)
    (read : mapList (getCell fr) args tested = .ok values readState)
    (entered : enterBlock fn fr target values readState = .ok (instsAt fn (target, 0), fr') after) :
    RuntimeFrameTy cfg fn activations fr' after := by
  have sameState := condition_state test
  subst tested
  obtain ⟨sourceValid, lastTerm⟩ := validated_instAt_term_last accepted member instruction
  obtain ⟨dest, lookup, argMetadata⟩ :=
    (validated_condbranch_metadata accepted member sourceValid lastTerm).1
  exact enterBranch_typed accepted member frameTyped lookup argMetadata read entered

theorem RuntimeStep.branchFalse_typed {cfg : GCfg} {activations : ActivationTypes} {fn : Func}
    {point : Pt} {fr fr' : Frame} {before tested readState after : St} {condition : ValueId}
    {target other : BlockId} {args otherArgs : List ValueId} {values : List RVal}
    (accepted : validate cfg.mod = .ok ()) (member : fn ∈ cfg.mod.allFuncs)
    (frameTyped : RuntimeFrameTy cfg fn activations fr before)
    (instruction : instAt fn point = some (.term (.condbr condition other otherArgs target args)))
    (test : (getVal fr condition >>= expectBool) before = .ok false tested)
    (read : mapList (getCell fr) args tested = .ok values readState)
    (entered : enterBlock fn fr target values readState = .ok (instsAt fn (target, 0), fr') after) :
    RuntimeFrameTy cfg fn activations fr' after := by
  have sameState := condition_state test
  subst tested
  obtain ⟨sourceValid, lastTerm⟩ := validated_instAt_term_last accepted member instruction
  obtain ⟨dest, lookup, argMetadata⟩ :=
    (validated_condbranch_metadata accepted member sourceValid lastTerm).2
  exact enterBranch_typed accepted member frameTyped lookup argMetadata read entered

theorem RuntimePoint.call_entry_typed {cfg : GCfg} {activations : ActivationTypes}
    {caller fn : Func} {point : Pt} {fr fr' : Frame} {before readState after : St}
    {result : ValueId} {callee : FnId} {args : List ValueId} {org : Option OriginId}
    {values : List Val}
    (accepted : validate cfg.mod = .ok ()) (reachable : RuntimePoint cfg caller point fr before)
    (callerTyped : RuntimeFrameTy cfg caller activations fr before)
    (instruction : instAt caller point = some (.def result (.call callee args org)))
    (read : mapList (getVal fr) args before = .ok values readState)
    (lookup : cfg.mod.funcs[callee]? = some fn)
    (entry : FunctionEntry fn (fr.depth + 1) values readState fr' after) :
    ∃ extended, (runtimeDeclarations cfg activations).Extends (runtimeDeclarations cfg extended) ∧
      RuntimeFrameTy cfg fn extended fr' after := by
  obtain ⟨block, blockMember, instructionMember⟩ := instAt_member instruction
  obtain ⟨checkedFn, checkedLookup, arity, operands, resultMetadata⟩ :=
    validated_call_operands accepted reachable.function_mem blockMember instructionMember
  have sameFn : checkedFn = fn := Option.some.inj (checkedLookup.symm.trans lookup)
  subst checkedFn
  obtain ⟨argsTyped, sameState⟩ := callerTyped.2.2.callArgs arity operands read
  subst readState
  have calleeMember : fn ∈ cfg.mod.allFuncs :=
    List.mem_append_left _ (Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup))
  obtain ⟨entryBlock, entryLookup, entryTypes⟩ := validated_entry_params accepted calleeMember
  exact entry.typed callerTyped.1 entryLookup
    (fun param present => validated_block_param_metadata accepted calleeMember
      (Array.mem_of_getElem? entryLookup) present)
    (argsTyped.entry entryTypes)

end Goose.Evidence
