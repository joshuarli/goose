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

def FunctionValueTy (roots : RootDeclarations) (fn : Func) (value : Val) : Prop :=
  match fn.results with
  | [] => value = .unit
  | [ty] => WeakValueTy roots value ty
  | _ => False

def EntryPreservation (cfg : GCfg) (fuel : Nat) : Prop :=
  ∀ (fn : Func) (depth : Nat) (args : List Val) (activations : ActivationTypes)
    (before after : St) (value : Val),
    fn ∈ cfg.mod.allFuncs → RuntimeStateTy cfg activations before →
    CallValuesTy (runtimeDeclarations cfg activations) fn.params args →
    Goose.GIR.enterFn fuel cfg depth fn args before = .ok value after →
    ∃ extended, activations.Extends extended ∧ RuntimeStateTy cfg extended after ∧
      FunctionValueTy (runtimeDeclarations cfg extended) fn value

def ExecPreservation (cfg : GCfg) (fuel : Nat) : Prop :=
  ∀ (fn : Func) (point : Pt) (fr : Frame) (activations : ActivationTypes)
    (before after : St) (value : Val),
    fn ∈ cfg.mod.allFuncs → RuntimeFrameTy cfg fn activations fr before →
    exec fuel ⟨cfg, fn⟩ fr (instsAt fn point) before = .ok value after →
    ∃ extended, activations.Extends extended ∧ RuntimeStateTy cfg extended after ∧
      FunctionValueTy (runtimeDeclarations cfg extended) fn value

theorem enterFn_typed_from_exec {cfg : GCfg} {fuel : Nat}
    (accepted : validate cfg.mod = .ok ())
    (bodyTyped : ∀ remaining, remaining < fuel → ExecPreservation cfg remaining) :
    EntryPreservation cfg fuel := by
  intro fn depth args activations before after value member stateTyped argsTyped evaluated
  obtain ⟨remaining, fr, entered, fuelEq, entry, executed⟩ := enterFn_success_entry evaluated
  obtain ⟨entryBlock, lookup, entryTypes⟩ := validated_entry_params accepted member
  obtain ⟨enteredActivations, rootExtension, activationExtension, frameTyped⟩ :=
    entry.typed stateTyped lookup
      (fun param present => validated_block_param_metadata accepted member
        (Array.mem_of_getElem? lookup) present) (argsTyped.entry entryTypes)
  obtain ⟨extended, bodyExtension, afterTyped, valueTyped⟩ :=
    bodyTyped remaining (by omega) fn (0, 0) fr enteredActivations entered after value
      member frameTyped executed
  exact ⟨extended, activationExtension.trans bodyExtension, afterTyped, valueTyped⟩

theorem execOp_result_typed {cfg : GCfg} {fn : Func} {activations : ActivationTypes}
    {point : Pt} {fr : Frame} {before after : St} {fuel : Nat} {result : ValueId}
    {op : Op} {ty : VTy} {cell : RVal}
    (accepted : validate cfg.mod = .ok ()) (member : fn ∈ cfg.mod.allFuncs)
    (frameTyped : RuntimeFrameTy cfg fn activations fr before)
    (instruction : instAt fn point = some (.def result op))
    (typed : op.resultTy { cfg.mod.tyEnv fn with vals := fn.valueTypes cfg.mod } = .ok ty)
    (metadata : (fn.valueTypes cfg.mod)[result]? = some (some ty))
    (entryTyped : ∀ remaining, remaining < fuel → EntryPreservation cfg remaining)
    (evaluated : execOp fuel ⟨cfg, fn⟩ fr op before = .ok cell after) :
    ∃ extended, activations.Extends extended ∧ RuntimeStateTy cfg extended after ∧
      WeakCellTy (runtimeDeclarations cfg extended) cell ty := by
  cases op with
  | call callee args origin =>
    obtain ⟨block, blockMember, instructionMember⟩ := instAt_member instruction
    obtain ⟨checkedFn, checkedLookup, arity, operands, resultMetadata⟩ :=
      validated_call_operands accepted member blockMember instructionMember
    cases fuel with
    | zero => simp [execOp, timeout, M.stop] at evaluated
    | succ remaining =>
      simp only [execOp] at evaluated
      obtain ⟨values, middle, read, evaluated⟩ := m_bind_ok evaluated
      obtain ⟨argsTyped, sameState⟩ := frameTyped.2.2.callArgs arity operands read
      subst middle
      obtain ⟨value, returned, called, evaluated⟩ := m_bind_ok evaluated
      simp only [pure_apply, Res.ok.injEq] at evaluated
      obtain ⟨rfl, rfl⟩ := evaluated
      obtain ⟨bodyFuel, calleeFn, callFuel, depth, lookup, entered⟩ := callFn_success_entry called
      have sameFn : calleeFn = checkedFn := Option.some.inj (lookup.symm.trans checkedLookup)
      subst calleeFn
      have calleeMember : checkedFn ∈ cfg.mod.allFuncs :=
        List.mem_append_left _ (Array.mem_toList_iff.mpr (Array.mem_of_getElem? checkedLookup))
      obtain ⟨extended, extension, stateTyped, valueTyped⟩ :=
        entryTyped bodyFuel (by omega) checkedFn (fr.depth + 1) values activations before returned value
          calleeMember frameTyped.1 argsTyped entered
      refine ⟨extended, extension, stateTyped, ?_⟩
      rcases resultMetadata with ⟨noResults, resultMetadata⟩ | ⟨returnTy, oneResult, resultMetadata⟩
      · have sameTy : ty = .data .unit := Option.some.inj (Option.some.inj
          (metadata.symm.trans resultMetadata))
        subst ty
        simpa only [FunctionValueTy, noResults, WeakCellTy, WeakValueTy] using valueTyped
      · have sameTy : ty = .data returnTy := Option.some.inj (Option.some.inj
          (metadata.symm.trans resultMetadata))
        subst ty
        simpa only [FunctionValueTy, oneResult, WeakCellTy] using valueTyped
  | _ =>
    simp only [execOp] at evaluated
    obtain ⟨cellTyped, stateTyped⟩ := execPure_result_typed frameTyped typed evaluated
    exact ⟨activations, .refl activations, stateTyped, cellTyped⟩

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

theorem exec_typed_from_smaller {cfg : GCfg} {fuel : Nat}
    (accepted : validate cfg.mod = .ok ())
    (smaller : ∀ remaining, remaining < fuel →
      ExecPreservation cfg remaining ∧ EntryPreservation cfg remaining) : ExecPreservation cfg fuel := by
  intro fn point fr activations before after value member frameTyped evaluated
  cases fuel with
  | zero => simp [exec, timeout, M.stop] at evaluated
  | succ remaining =>
    cases suffix : instsAt fn point with
    | nil => simp [exec, suffix, fault, M.stop] at evaluated
    | cons instruction rest =>
      obtain ⟨atPoint, nextSuffix⟩ := instsAt_cons_inverse suffix
      obtain ⟨block, blockMember, instructionMember⟩ := instAt_member atPoint
      have bodyTyped := (smaller remaining (Nat.lt_succ_self _)).1
      cases instruction with
      | «def» result op =>
        obtain ⟨resultTy, opTyped, resultMetadata⟩ :=
          (validate_sound cfg.mod accepted).1 fn member |>.2.1 block blockMember result op instructionMember
        simp only [exec, suffix] at evaluated
        obtain ⟨cell, middle, executedOp, evaluated⟩ := m_bind_ok evaluated
        obtain ⟨intermediate, extension, stateTyped, cellTyped⟩ :=
          execOp_result_typed accepted member frameTyped atPoint opTyped resultMetadata
            (fun subfuel bound => (smaller subfuel (Nat.lt_trans bound (Nat.lt_succ_self _))).2) executedOp
        have callerTyped := frameTyped.transfer extension stateTyped
        have nextTyped : RuntimeFrameTy cfg fn intermediate (fr.set result cell) middle :=
          ⟨callerTyped.1, callerTyped.2.1, callerTyped.2.2.set resultMetadata cellTyped⟩
        simp only [setCell, pure_bind] at evaluated
        rw [nextSuffix] at evaluated
        obtain ⟨extended, bodyExtension, afterTyped, valueTyped⟩ :=
          bodyTyped fn (point.1, point.2 + 1) (fr.set result cell) intermediate middle after value
            member nextTyped evaluated
        exact ⟨extended, extension.trans bodyExtension, afterTyped, valueTyped⟩
      | eff effect =>
        have effectTyped := validated_effect_types accepted member blockMember instructionMember
        simp only [exec, suffix] at evaluated
        obtain ⟨nextFrame, middle, executedEffect, evaluated⟩ := m_bind_ok evaluated
        have nextTyped := execEff_result_typed frameTyped effectTyped executedEffect
        rw [nextSuffix] at evaluated
        exact bodyTyped fn (point.1, point.2 + 1) nextFrame activations middle after value member nextTyped evaluated
      | term term =>
        cases term with
        | br target args =>
          simp only [exec, suffix] at evaluated
          obtain ⟨values, readState, read, evaluated⟩ := m_bind_ok evaluated
          obtain ⟨pair, enteredState, entered, evaluated⟩ := m_bind_ok evaluated
          obtain ⟨instructions, nextFrame⟩ := pair
          have instructionsEq := enterBlock_instructions entered
          rw [instructionsEq] at entered evaluated
          have nextTyped := RuntimeStep.branch_typed accepted member frameTyped atPoint read entered
          exact bodyTyped fn (target, 0) nextFrame activations enteredState after value member nextTyped evaluated
        | condbr condition trueTarget trueArgs falseTarget falseArgs =>
          simp only [exec, suffix] at evaluated
          obtain ⟨conditionValue, readState, read, evaluated⟩ := m_bind_ok evaluated
          obtain ⟨testValue, testedState, tested, evaluated⟩ := m_bind_ok evaluated
          have conditionResult : (getVal fr condition >>= expectBool) before = .ok testValue testedState := by
            rw [bind_apply, read]
            exact tested
          have sameState := condition_state conditionResult
          subst testedState
          cases testValue with
          | true =>
            simp only [↓reduceIte] at evaluated
            obtain ⟨values, readState, read, evaluated⟩ := m_bind_ok evaluated
            obtain ⟨pair, enteredState, entered, evaluated⟩ := m_bind_ok evaluated
            obtain ⟨instructions, nextFrame⟩ := pair
            have instructionsEq := enterBlock_instructions entered
            rw [instructionsEq] at entered evaluated
            have nextTyped := RuntimeStep.branchTrue_typed accepted member frameTyped atPoint conditionResult read entered
            exact bodyTyped fn (trueTarget, 0) nextFrame activations enteredState after value member nextTyped evaluated
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at evaluated
            obtain ⟨values, readState, read, evaluated⟩ := m_bind_ok evaluated
            obtain ⟨pair, enteredState, entered, evaluated⟩ := m_bind_ok evaluated
            obtain ⟨instructions, nextFrame⟩ := pair
            have instructionsEq := enterBlock_instructions entered
            rw [instructionsEq] at entered evaluated
            have nextTyped := RuntimeStep.branchFalse_typed accepted member frameTyped atPoint conditionResult read entered
            exact bodyTyped fn (falseTarget, 0) nextFrame activations enteredState after value member nextTyped evaluated
        | ret values origin =>
          obtain ⟨arity, metadata⟩ := validated_ret_metadata accepted member blockMember instructionMember
          simp only [exec, suffix] at evaluated
          cases values with
          | nil =>
            have noResults : fn.results = [] := List.length_eq_zero_iff.mp arity.symm
            simp only [pure_apply, Res.ok.injEq] at evaluated
            obtain ⟨rfl, rfl⟩ := evaluated
            exact ⟨activations, .refl activations, frameTyped.1, by simp [FunctionValueTy, noResults]⟩
          | cons id rest =>
            cases rest with
            | cons next rest => simp [fault, M.stop] at evaluated
            | nil =>
              cases resultTypes : fn.results with
              | nil => simp [resultTypes] at arity
              | cons resultTy rest =>
                cases rest with
                | cons next rest => simp [resultTypes] at arity
                | nil =>
                  have valueMetadata := metadata (id, resultTy) (by simp [resultTypes])
                  obtain ⟨valueTyped, sameState⟩ := frameTyped.2.2.getVal valueMetadata evaluated
                  subst after
                  exact ⟨activations, .refl activations, frameTyped.1,
                    by simpa only [FunctionValueTy, resultTypes] using valueTyped⟩
        | abort kind origin =>
          cases origin <;> simp [exec, suffix, abortAtOrg, abortAt, fault, M.stop] at evaluated
        | exit id origin =>
          simp only [exec, suffix] at evaluated
          obtain ⟨exitValue, middle, read, evaluated⟩ := m_bind_ok evaluated
          obtain ⟨integer, middle, checked, evaluated⟩ := m_bind_ok evaluated
          simp [M.stop] at evaluated
        | unreachable => simp [exec, suffix, fault, M.stop] at evaluated

theorem successful_functions_typed {cfg : GCfg} (accepted : validate cfg.mod = .ok ()) (fuel : Nat) :
    ExecPreservation cfg fuel ∧ EntryPreservation cfg fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    exact ⟨exec_typed_from_smaller accepted ih,
      enterFn_typed_from_exec accepted (fun remaining bound => (ih remaining bound).1)⟩

private theorem moduleSignatures {m : GIR.Module} (accepted : validate m = .ok ()) :
    (∃ entry, m.funcs[m.entry]? = some entry ∧ entry.params = [] ∧ entry.results = []) ∧
    (∀ global ∈ m.globals, global.init.params = [] ∧ global.init.results = [global.ty]) := by
  unfold Goose.GIR.validate at accepted
  obtain ⟨_, signatures, _⟩ := bind_ok accepted
  unfold checkEntryAndGlobals at signatures
  cases lookup : m.funcs[m.entry]? with
  | none => simp [lookup, violation, bind, Except.bind] at signatures
  | some entry =>
    have entrySignature : (entry.params.isEmpty && entry.results.isEmpty) = true := by
      by_cases entrySignature : (entry.params.isEmpty && entry.results.isEmpty) = true
      · exact entrySignature
      · simp [lookup, entrySignature, violation, bind, Except.bind] at signatures
    simp only [lookup, entrySignature, ↓reduceIte] at signatures
    obtain ⟨_, globalsChecked, _⟩ := bind_ok signatures
    refine ⟨⟨entry, rfl, ?_⟩, ?_⟩
    · simpa only [Bool.and_eq_true, List.isEmpty_iff] using entrySignature
    rw [← Array.forIn_toList] at globalsChecked
    have all := forIn_yielded globalsChecked (by
      intro global accumulator step checked
      by_cases signature : (global.init.params.isEmpty && (global.init.results == [global.ty])) = true
      · simp only [signature, ↓reduceIte] at checked
        by_cases origin : global.org < m.origins.size
        · simpa [origin, pure, Except.pure] using checked.symm
        · simp [origin, violation, bind, Except.bind] at checked
      · simp [signature, violation, bind, Except.bind] at checked)
    intro global member
    have checked := all global (Array.mem_toList_iff.mpr member)
    have signature : (global.init.params.isEmpty && (global.init.results == [global.ty])) = true := by
      by_cases signature : (global.init.params.isEmpty && (global.init.results == [global.ty])) = true
      · exact signature
      · simp [signature, violation, bind, Except.bind] at checked
    simpa only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] using signature

theorem initGlobals_typed {cfg : GCfg} {fuel : Nat} {ids : List GlobalId}
    {activations : ActivationTypes} {before after : St}
    (accepted : validate cfg.mod = .ok ()) (stateTyped : RuntimeStateTy cfg activations before)
    (initialized : initGlobals fuel cfg ids before = .ok () after) :
    ∃ extended, activations.Extends extended ∧ RuntimeStateTy cfg extended after := by
  induction ids generalizing activations before with
  | nil =>
    simp only [Goose.GIR.initGlobals, pure_apply, Res.ok.injEq] at initialized
    obtain ⟨_, sameState⟩ := initialized
    subst after
    exact ⟨activations, .refl activations, stateTyped⟩
  | cons id rest ih =>
    simp only [Goose.GIR.initGlobals] at initialized
    obtain ⟨init, middle, found, initialized⟩ := m_bind_ok initialized
    cases lookup : cfg.mod.globals[id]? with
    | none => simp [lookupInit, lookup, fault, M.stop] at found
    | some global =>
      simp only [lookupInit, lookup, pure_apply, Res.ok.injEq] at found
      obtain ⟨sameFn, sameState⟩ := found
      have fnEq : init = global.init := sameFn.symm
      have stateEq : middle = before := sameState.symm
      subst init
      subst middle
      obtain ⟨value, returned, entered, initialized⟩ := m_bind_ok initialized
      have globalMember := Array.mem_of_getElem? lookup
      obtain ⟨noParams, resultType⟩ := (moduleSignatures accepted).2 global globalMember
      have initMember : global.init ∈ cfg.mod.allFuncs := by
        simp only [Module.allFuncs, List.mem_append, List.mem_map]
        exact Or.inr ⟨global, Array.mem_toList_iff.mpr globalMember, rfl⟩
      have argsTyped : CallValuesTy (runtimeDeclarations cfg activations) global.init.params [] := by
        rw [noParams]
        exact .nil
      obtain ⟨intermediate, extension, returnedTyped, valueTyped⟩ :=
        (successful_functions_typed accepted fuel).2 global.init 0 [] activations before returned value
          initMember stateTyped argsTyped entered
      have globalValueTyped : WeakValueTy (runtimeDeclarations cfg intermediate) value global.ty := by
        simpa only [FunctionValueTy, resultType] using valueTyped
      have declaration : runtimeDeclarations cfg intermediate (.global id) = some global.ty := by
        simp [runtimeDeclarations, lookup]
      have boundTyped : RuntimeStateTy cfg intermediate
          { returned with store := returned.store.introduce (.global id) value } :=
        ⟨returnedTyped.1, returnedTyped.2.introduce declaration globalValueTyped⟩
      simp only [bindRoot, bind_apply] at initialized
      obtain ⟨extended, restExtension, finalTyped⟩ := ih boundTyped initialized
      exact ⟨extended, extension.trans restExtension, finalTyped⟩

theorem RuntimePoint.typed {cfg : GCfg} {fn : Func} {point : Pt} {fr : Frame} {state : St}
    (accepted : validate cfg.mod = .ok ()) (reachable : RuntimePoint cfg fn point fr state) :
    ∃ activations, RuntimeFrameTy cfg fn activations fr state := by
  induction reachable with
  | @initializer fuel index before global fr after positive valid initialized lookup entry =>
    obtain ⟨activations, extension, beforeTyped⟩ := initGlobals_typed accepted
      (RuntimeStateTy.initial cfg) initialized
    have globalMember := Array.mem_of_getElem? lookup
    have member : global.init ∈ cfg.mod.allFuncs := by
      simp only [Module.allFuncs, List.mem_append, List.mem_map]
      exact Or.inr ⟨global, Array.mem_toList_iff.mpr globalMember, rfl⟩
    have noParams := ((moduleSignatures accepted).2 global globalMember).1
    have argsTyped : CallValuesTy (runtimeDeclarations cfg activations) global.init.params [] := by
      rw [noParams]
      exact .nil
    obtain ⟨entryBlock, entryLookup, entryTypes⟩ := validated_entry_params accepted member
    obtain ⟨extended, rootExtension, activationExtension, typed⟩ :=
      entry.typed beforeTyped entryLookup
        (fun param present => validated_block_param_metadata accepted member
          (Array.mem_of_getElem? entryLookup) present) (argsTyped.entry entryTypes)
    exact ⟨extended, typed⟩
  | @entry fuel before fn fr after positive initialized lookup entry =>
    obtain ⟨activations, extension, beforeTyped⟩ := initGlobals_typed accepted
      (RuntimeStateTy.initial cfg) initialized
    have member : fn ∈ cfg.mod.allFuncs :=
      List.mem_append_left _ (Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup))
    obtain ⟨checkedEntry, checkedLookup, noParams, noResults⟩ := (moduleSignatures accepted).1
    have sameFn : checkedEntry = fn := Option.some.inj (checkedLookup.symm.trans lookup)
    subst checkedEntry
    have argsTyped : CallValuesTy (runtimeDeclarations cfg activations) fn.params [] := by
      rw [noParams]
      exact .nil
    obtain ⟨entryBlock, entryLookup, entryTypes⟩ := validated_entry_params accepted member
    obtain ⟨extended, rootExtension, activationExtension, typed⟩ :=
      entry.typed beforeTyped entryLookup
        (fun param present => validated_block_param_metadata accepted member
          (Array.mem_of_getElem? entryLookup) present) (argsTyped.entry entryTypes)
    exact ⟨extended, typed⟩
  | call callerPoint instruction depth read lookup entry ih =>
    obtain ⟨activations, callerTyped⟩ := ih
    obtain ⟨extended, rootExtension, activationExtension, typed⟩ :=
      RuntimePoint.call_entry_typed accepted callerPoint callerTyped instruction read lookup entry
    exact ⟨extended, typed⟩
  | step before transition ih =>
    obtain ⟨activations, beforeTyped⟩ := ih
    have member := before.function_mem
    cases transition with
    | define instruction evaluated =>
      obtain ⟨block, blockMember, instructionMember⟩ := instAt_member instruction
      obtain ⟨ty, opTyped, resultMetadata⟩ :=
        (validate_sound cfg.mod accepted).1 _ member |>.2.1 block blockMember _ _ instructionMember
      obtain ⟨extended, extension, stateTyped, valueTyped⟩ :=
        execOp_result_typed accepted member beforeTyped instruction opTyped resultMetadata
          (fun fuel bound => (successful_functions_typed accepted fuel).2) evaluated
      have transferred := beforeTyped.transfer extension stateTyped
      exact ⟨extended, transferred.1, transferred.2.1, transferred.2.2.set resultMetadata valueTyped⟩
    | effect instruction evaluated =>
      obtain ⟨block, blockMember, instructionMember⟩ := instAt_member instruction
      exact ⟨activations, execEff_result_typed beforeTyped
        (validated_effect_types accepted member blockMember instructionMember) evaluated⟩
    | branch instruction read entered =>
      exact ⟨activations, RuntimeStep.branch_typed accepted member beforeTyped instruction read entered⟩
    | branchTrue instruction tested read entered =>
      exact ⟨activations, RuntimeStep.branchTrue_typed accepted member beforeTyped instruction tested read entered⟩
    | branchFalse instruction tested read entered =>
      exact ⟨activations, RuntimeStep.branchFalse_typed accepted member beforeTyped instruction tested read entered⟩

theorem RuntimePoint.int {cfg : GCfg} {fn : Func} {point : Pt} {fr : Frame} {state : St}
    {id : ValueId} {ty : IntTy} {cell : RVal}
    (accepted : validate cfg.mod = .ok ()) (reachable : RuntimePoint cfg fn point fr state)
    (metadata : (fn.valueTypes cfg.mod)[id]? = some (some (.data (.int ty))))
    (present : fr.vals[id]? = some cell) :
    ∃ value, fr.vals[id]? = some (.val (.int ty value)) := by
  obtain ⟨activations, typed⟩ := reachable.typed accepted
  exact typed.2.2.int metadata present

end Goose.Evidence
