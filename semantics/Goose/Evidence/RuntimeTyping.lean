import Goose.Evidence.Typing
import Goose.Evidence.TypingValidation

namespace Goose.Evidence

open Goose.Core Goose.GIR

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
