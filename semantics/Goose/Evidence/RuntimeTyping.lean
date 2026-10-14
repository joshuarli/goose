import Goose.Evidence.Typing
import Goose.Evidence.TypingValidation
import Goose.Evidence.TypingViews
import Goose.Evidence.TypingMetadata

namespace Goose.Evidence

open Goose.Core Goose.GIR

private theorem forIn_yielded {ε α : Type} {xs : List α}
    {f : α → PUnit.{1} → Except ε (ForInStep PUnit.{1})}
    (checked : forIn xs PUnit.unit f = .ok ())
    (yielded : ∀ value accumulator step, f value accumulator = .ok step → step = .yield PUnit.unit) :
    ∀ value ∈ xs, f value PUnit.unit = .ok (.yield PUnit.unit) := by
  induction xs with
  | nil => simp
  | cons value rest ih =>
    rw [List.forIn_cons] at checked
    obtain ⟨step, head, tail⟩ := bind_ok checked
    have same := yielded value PUnit.unit step head
    subst step
    intro other present
    rcases List.mem_cons.mp present with rfl | present
    · exact head
    · exact ih tail other present

private theorem map_equal_from_zip {α β γ : Type} {xs : List α} {ys : List β}
    {left : α → γ} {right : β → γ} (count : xs.length = ys.length)
    (matched : ∀ pair ∈ xs.zip ys, left pair.1 = right pair.2) : xs.map left = ys.map right := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons head tail ih =>
    cases ys with
    | nil => simp at count
    | cons other rest =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at count
      have same := matched (head, other) (by simp)
      have tailSame := ih count (fun pair present => matched pair (by simp [present]))
      simp only [List.map_cons, same, tailSame]

private theorem structResult_metadata {env : TyEnv} {ty : Ty} {values : List ValueId}
    {result : VTy} (typed : (Op.structLit ty values).resultTy env = .ok result) :
    ∃ sid fields, ty = .structT sid fields ∧ result = .data ty ∧
      values.map (fun id => env.vals[id]?) = fields.toList.map (fun fieldTy => some (some (.data fieldTy))) := by
  cases ty with
  | structT sid fields =>
    simp only [Op.resultTy] at typed
    cases lookup : env.structs[sid]? with
    | none => simp [lookup, tyErr] at typed
    | some descriptor =>
      rw [lookup] at typed
      dsimp only at typed
      have payload : fields = TyList.ofList (descriptor.fields.toList.map (·.ty)) := by
        by_cases same : fields = TyList.ofList (descriptor.fields.toList.map (·.ty))
        · exact same
        · simp [same, tyErr, bind, Except.bind] at typed
      simp only [payload, beq_self_eq_true, ↓reduceIte] at typed
      have count : values.length = descriptor.fields.size := by
        by_cases same : values.length = descriptor.fields.size
        · exact same
        · simp [same, tyErr, bind, Except.bind] at typed
      simp only [count, beq_self_eq_true, ↓reduceIte] at typed
      obtain ⟨accumulator, loop, resultTyped⟩ := bind_ok typed
      cases accumulator
      have all := forIn_yielded loop (by
        intro pair accumulator step checked
        obtain ⟨fieldTy, read, checked⟩ := bind_ok checked
        by_cases same : fieldTy = pair.2.ty
        · simpa [same, pure, Except.pure] using checked.symm
        · simp [same, tyErr, bind, Except.bind] at checked)
      refine ⟨sid, fields, rfl, ?_, ?_⟩
      · simpa only [payload] using (Except.ok.inj resultTyped).symm
      · simp only [payload, Goose.Core.Sound.tyList_toList_ofList, List.map_map]
        apply map_equal_from_zip (by simpa using count)
        intro pair present
        have checked := all pair present
        obtain ⟨fieldTy, read, checked⟩ := bind_ok checked
        have same : fieldTy = pair.2.ty := by
          by_cases same : fieldTy = pair.2.ty
          · exact same
          · simp [same, tyErr, bind, Except.bind] at checked
        subst fieldTy
        exact dataTy_of read
  | _ => simp [Op.resultTy, tyErr] at typed

private theorem pureResult_state {cfg : GCfg} {activations : ActivationTypes}
    {before after : St} {cell : RVal} {ty : VTy}
    (stateTyped : RuntimeStateTy cfg activations before)
    (result : WeakCellTy (runtimeDeclarations cfg activations) cell ty ∧ after = before) :
    WeakCellTy (runtimeDeclarations cfg activations) cell ty ∧ RuntimeStateTy cfg activations after :=
  ⟨result.1, result.2 ▸ stateTyped⟩

theorem execPure_result_typed {cfg : GCfg} {fn : Func} {activations : ActivationTypes}
    {fr : Frame} {before after : St} {op : Op} {ty : VTy} {cell : RVal}
    (frameTyped : RuntimeFrameTy cfg fn activations fr before)
    (typed : op.resultTy { cfg.mod.tyEnv fn with vals := fn.valueTypes cfg.mod } = .ok ty)
    (evaluated : execPure ⟨cfg, fn⟩ fr op before = .ok cell after) :
    WeakCellTy (runtimeDeclarations cfg activations) cell ty ∧ RuntimeStateTy cfg activations after := by
  cases op with
  | constInt intTy value =>
    obtain ⟨range, rfl⟩ := constInt_metadata typed
    exact pureResult_state frameTyped.1 (execPure_constInt_typed evaluated)
  | constBool value =>
    have result := constBool_metadata typed
    subst ty
    exact pureResult_state frameTyped.1 (execPure_constBool_typed evaluated)
  | constUnit =>
    have result := constUnit_metadata typed
    subst ty
    exact pureResult_state frameTyped.1 (execPure_constUnit_typed evaluated)
  | bin operator intTy left right origin =>
    obtain ⟨leftMetadata, rightMetadata, rfl⟩ := bin_metadata typed
    exact pureResult_state frameTyped.1
      (execPure_bin_typed frameTyped.2.2 leftMetadata rightMetadata evaluated)
  | un operator intTy operand origin =>
    obtain ⟨metadata, rfl⟩ := un_metadata typed
    exact pureResult_state frameTyped.1 (execPure_un_typed frameTyped.2.2 metadata evaluated)
  | cmp operator intTy left right =>
    obtain ⟨leftMetadata, rightMetadata, rfl⟩ := cmp_metadata typed
    exact pureResult_state frameTyped.1 (execPure_cmp_typed evaluated)
  | boolCmp operator left right =>
    obtain ⟨leftMetadata, rightMetadata, rfl⟩ := boolCmp_metadata typed
    exact pureResult_state frameTyped.1 (execPure_boolCmp_typed evaluated)
  | boolNot operand =>
    obtain ⟨metadata, rfl⟩ := boolNot_metadata typed
    exact pureResult_state frameTyped.1 (execPure_boolNot_typed frameTyped.2.2 metadata evaluated)
  | conv conversion source target operand origin =>
    obtain ⟨metadata, rfl⟩ := conv_metadata typed
    exact pureResult_state frameTyped.1 (execPure_conv_typed frameTyped.2.2 metadata evaluated)
  | next intTy operand =>
    obtain ⟨metadata, rfl⟩ := next_metadata typed
    exact pureResult_state frameTyped.1 (execPure_next_typed frameTyped.2.2 metadata evaluated)
  | slotAddr slotId =>
    obtain ⟨slot, permission, lookup, rfl⟩ := slotAddr_metadata typed
    exact pureResult_state frameTyped.1 (execPure_slotAddr_typed frameTyped.2.1 lookup evaluated permission)
  | globalAddr globalId =>
    obtain ⟨target, kind, permission, lookup, rfl⟩ := globalAddr_metadata typed
    change (cfg.mod.globals.map (fun global => (global.ty, global.kind)))[globalId]? = some (target, kind) at lookup
    cases globalLookup : cfg.mod.globals[globalId]? with
    | none => simp [globalLookup] at lookup
    | some global =>
      have same : (global.ty, global.kind) = (target, kind) := by simpa [globalLookup] using lookup
      obtain ⟨rfl, rfl⟩ := same
      exact pureResult_state frameTyped.1 (execPure_globalAddr_typed globalLookup evaluated permission)
  | refElem viewId indexId =>
    obtain ⟨permission, element, indexTy, viewMetadata, indexMetadata, rfl⟩ := refElem_metadata typed
    exact pureResult_state frameTyped.1
      (execPure_refElem_typed frameTyped.2.2 viewMetadata indexMetadata evaluated)
  | refFreeze reference =>
    obtain ⟨permission, target, metadata, rfl⟩ := refFreeze_metadata typed
    exact pureResult_state frameTyped.1 (execPure_refFreeze_typed frameTyped.2.2 metadata evaluated)
  | load reference =>
    obtain ⟨permission, target, metadata, rfl⟩ := load_metadata typed
    exact pureResult_state frameTyped.1
      (execPure_load_typed frameTyped.2.2 metadata frameTyped.1.2 evaluated)
  | snapshot mode reference =>
    obtain ⟨permission, owner, element, resultPermission, metadata, arrayType, rfl⟩ := snapshot_metadata typed
    exact pureResult_state frameTyped.1 (execPure_snapshot_typed frameTyped.2.2 metadata arrayType evaluated)
  | sliceView sliceId =>
    obtain ⟨permission, element, metadata, rfl⟩ := sliceView_metadata typed
    exact pureResult_state frameTyped.1 (execPure_sliceView_typed frameTyped.2.2 metadata evaluated)
  | viewLen viewId =>
    obtain ⟨permission, element, metadata, rfl⟩ := viewLen_metadata typed
    exact pureResult_state frameTyped.1 (execPure_viewLen_typed evaluated)
  | viewSlice permission viewId lo hi origin =>
    obtain ⟨sourcePermission, element, metadata, loMetadata, hiMetadata, rfl⟩ := viewSlice_metadata typed
    exact pureResult_state frameTyped.1 (execPure_viewSlice_typed frameTyped.2.2 metadata evaluated)
  | arrayLen reference =>
    obtain ⟨permission, owner, element, metadata, arrayType, rfl⟩ := arrayLen_metadata typed
    exact pureResult_state frameTyped.1 (execPure_arrayLen_typed evaluated)
  | indexChecked viewId indexId origin =>
    obtain ⟨permission, element, indexTy, viewMetadata, indexMetadata, rfl⟩ := indexChecked_metadata typed
    exact pureResult_state frameTyped.1
      (execPure_indexChecked_typed frameTyped.2.2 viewMetadata indexMetadata evaluated)
  | indexProven viewId indexId =>
    obtain ⟨permission, element, indexTy, viewMetadata, indexMetadata, rfl⟩ := indexProven_metadata typed
    exact pureResult_state frameTyped.1
      (execPure_indexProven_typed frameTyped.2.2 viewMetadata indexMetadata evaluated)
  | push reference value origin =>
    obtain ⟨permission, owner, element, refMetadata, ownerType, valueMetadata, rfl⟩ := push_metadata typed
    exact execPure_push_typed frameTyped refMetadata valueMetadata ownerType evaluated
  | pop reference origin =>
    obtain ⟨permission, owner, element, metadata, ownerType, rfl⟩ := pop_metadata typed
    obtain ⟨valueTyped, storeTyped, sameAllocation⟩ :=
      execPure_pop_typed frameTyped.2.2 metadata ownerType frameTyped.1.2 evaluated
    exact ⟨valueTyped, sameAllocation ▸ frameTyped.1.1, storeTyped⟩
  | call callee args origin => simp [execPure, fault, M.stop] at evaluated
  | arrLit arrayTy values =>
    obtain ⟨element, arrayType, metadata, fixedCount, capacity, rfl⟩ := arrLit_metadata typed
    exact pureResult_state frameTyped.1
      (execPure_arrLit_typed frameTyped.2.2 metadata arrayType fixedCount evaluated)
  | structLit structTy values =>
    obtain ⟨sid, fields, rfl, rfl, metadata⟩ := structResult_metadata typed
    exact pureResult_state frameTyped.1
      (execPure_structLit_typed frameTyped.2.2 (FieldOperands.ofMap metadata) evaluated)
  | fieldAddr owner index =>
    obtain ⟨permission, sid, fields, descriptor, field, metadata, lookup, selector, logicalField, rfl⟩ :=
      fieldAddr_metadata typed
    exact pureResult_state frameTyped.1
      (execPure_fieldAddr_typed frameTyped.2.2 metadata logicalField evaluated)
  | arrFill arrayTy operand =>
    obtain ⟨element, count, rfl, metadata, rfl⟩ := arrFill_metadata typed
    exact pureResult_state frameTyped.1 (execPure_arrFill_typed frameTyped.2.2 metadata evaluated)

theorem execEff_result_typed {cfg : GCfg} {fn : Func} {activations : ActivationTypes}
    {fr fr' : Frame} {before after : St} {effect : Effect}
    (frameTyped : RuntimeFrameTy cfg fn activations fr before)
    (typed : checkEffectTypes { cfg.mod.tyEnv fn with vals := fn.valueTypes cfg.mod } effect = .ok ())
    (evaluated : execEff fn fr effect before = .ok fr' after) :
    RuntimeFrameTy cfg fn activations fr' after := by
  cases effect with
  | slotInit id value origin =>
    simp only [checkEffectTypes] at typed
    cases lookup : fn.slots[id]? with
    | none => simp only [typing_env_slots, lookup] at typed; simp [tyErr] at typed
    | some slot =>
      simp only [typing_env_slots, lookup] at typed
      obtain ⟨valueTy, valueMetadata, typed⟩ := bind_ok typed
      have same : valueTy = slot.ty := by
        by_cases same : valueTy = slot.ty
        · exact same
        · simp [same, tyErr] at typed
      subst valueTy
      exact execEff_slotInit_typed frameTyped lookup (dataTy_of valueMetadata) evaluated
  | store reference value origin =>
    simp only [checkEffectTypes] at typed
    obtain ⟨⟨permission, target⟩, referenceMetadata, typed⟩ := bind_ok typed
    obtain ⟨valueTy, valueMetadata, typed⟩ := bind_ok typed
    have same : valueTy = target := by
      by_cases same : valueTy = target
      · exact same
      · simp [same, tyErr] at typed
    subst valueTy
    exact execEff_store_typed frameTyped (refTy_metadata referenceMetadata) (dataTy_of valueMetadata) evaluated
  | append reference view origin =>
    simp only [checkEffectTypes] at typed
    obtain ⟨⟨permission, owner⟩, referenceMetadata, typed⟩ := bind_ok typed
    cases owner with
    | grow element | growshrink element | limited element capacity =>
      obtain ⟨⟨viewPermission, viewElement⟩, viewMetadata, typed⟩ := bind_ok typed
      have same : viewElement = element := by
        by_cases same : viewElement = element
        · exact same
        · simp [same, tyErr] at typed
      subst viewElement
      exact execEff_append_typed frameTyped (refTy_metadata referenceMetadata)
        (viewTy_metadata viewMetadata) rfl evaluated
    | _ => simp [tyErr] at typed
  | popN reference count origin =>
    simp only [checkEffectTypes] at typed
    obtain ⟨⟨permission, owner⟩, referenceMetadata, typed⟩ := bind_ok typed
    cases ownerType : owner.ownerElem? with
    | none => simp [ownerType, tyErr, bind, Except.bind] at typed
    | some element =>
      simp only [ownerType, Option.isSome_some, ↓reduceIte] at typed
      obtain ⟨countTy, countMetadata, result⟩ := bind_ok typed
      exact execEff_popN_typed frameTyped (refTy_metadata referenceMetadata)
        (intTy_of countMetadata) ownerType evaluated
  | resize reference size fill origin =>
    simp only [checkEffectTypes] at typed
    obtain ⟨⟨permission, owner⟩, referenceMetadata, typed⟩ := bind_ok typed
    cases ownerType : owner.ownerElem? with
    | none => simp [ownerType, tyErr] at typed
    | some element =>
      simp only [ownerType] at typed
      obtain ⟨sizeTy, sizeMetadata, typed⟩ := bind_ok typed
      have fillMetadata : ∀ id, fill = some id →
          (fn.valueTypes cfg.mod)[id]? = some (some (.data element)) := by
        cases fill with
        | none => intro id impossible; cases impossible
        | some fillId =>
          intro id sameId
          cases sameId
          obtain ⟨valueTy, valueMetadata, typed⟩ := bind_ok typed
          have same : valueTy = element := by
            by_cases same : valueTy = element
            · exact same
            · simp [same, tyErr] at typed
          subst valueTy
          exact dataTy_of valueMetadata
      exact execEff_resize_typed frameTyped (refTy_metadata referenceMetadata)
        (intTy_of sizeMetadata) fillMetadata ownerType evaluated
  | clear reference origin =>
    simp only [checkEffectTypes] at typed
    obtain ⟨⟨permission, owner⟩, referenceMetadata, typed⟩ := bind_ok typed
    cases ownerType : owner.ownerElem? with
    | none => simp [ownerType, tyErr] at typed
    | some element =>
      exact execEff_clear_typed frameTyped (refTy_metadata referenceMetadata) ownerType evaluated
  | replace reference value origin =>
    simp only [checkEffectTypes] at typed
    obtain ⟨⟨permission, owner⟩, referenceMetadata, typed⟩ := bind_ok typed
    have valueTypeChecked : ∃ valueTy,
        ({ cfg.mod.tyEnv fn with vals := fn.valueTypes cfg.mod } : TyEnv).dataTy value = .ok valueTy ∧
        valueTy = owner := by
      cases owner with
      | grow element | growshrink element =>
        obtain ⟨valueTy, valueMetadata, typed⟩ := bind_ok typed
        split at typed
        · rename_i same
          exact ⟨valueTy, valueMetadata, same⟩
        · simp [tyErr] at typed
      | _ => simp [tyErr, bind, Except.bind] at typed
    obtain ⟨valueTy, valueMetadata, rfl⟩ := valueTypeChecked
    exact execEff_replace_typed frameTyped (refTy_metadata referenceMetadata)
      (dataTy_of valueMetadata) evaluated
  | enter scope => exact execEff_enter_typed frameTyped evaluated
  | leave scope => exact execEff_leave_typed frameTyped evaluated
  | print parts origin => exact execEff_print_typed frameTyped evaluated

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
      activations.Extends extended ∧ RuntimeFrameTy cfg fn extended fr' after := by
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
