import Goose.Lower.Validation.PermissionPreservationEachSource
import Goose.Lower.Validation.PermissionPreservationFreshBorrow
import Goose.Lower.Validation.PermissionPreservationFreshOperations
import Goose.Lower.Validation.PermissionInstructionReferencesBorrow
import Goose.Lower.Validation.ExpressionContentsRules
import Goose.Core.Sound.Check

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem PermissionTransfer.mutable_reference {profile : ArtifactProfile}
    {writable contents : ValueId → Prop} {value : ValueId} {target : Ty}
    (binding : writable value) (elements : contents value) :
    PermissionTransfer profile writable contents value (.ref .mutable target) := by
  cases profile <;> cases target <;> simp only [PermissionTransfer, reduceCtorEq, ↓reduceIte] <;>
    first | exact binding | exact elements | exact ⟨binding, elements⟩

theorem borrowTo_mutable_reference_permissions {le : LEnv} {first : Nat} {before after : LS}
    {owner value : ValueId} {target : Ty} {block : BlockId}
    (bindings : FreshWritableEvidence le first before owner)
    (contents : FreshContentsEvidence le first before owner)
    (typed : before.vals[owner]? = some (some (.data (.ref .mutable target))))
    (generated : GeneratedBuilderState before) (live : before.cur = some block)
    (run : borrowTo .mutable owner le before = (value, after)) :
    FreshWritableEvidence le first after value ∧ FreshContentsEvidence le first after value := by
  cases profile : le.mod.profile <;> cases target <;>
    simp [borrowTo, bind_run, read_apply, valTy_of_recorded typed, profile, freezeTo, pure_run] at run
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := run; exact ⟨bindings, contents⟩)
    | exact contents.ownerBorrow_permissions generated.dense generated.live live run

theorem eachElemValue_permissionInstructions_transfer
    {le : LEnv} {slot : SlotId} {localVar : LocalVar} {element : Ty} {writable byRef : Bool}
    {sourceCounter : Nat} (row : le.vars[slot]? = some localVar)
    (source : Core.loopVarOk localVar byRef element writable sourceCounter = .ok ((), sourceCounter))
    {module : GIR.Module} {func : Func} {first : Nat} {before after : LS} {owner value : ValueId}
    {actual : Mutability} {block : BlockId}
    (typed : before.vals[owner]? = some (some (.data (.ref actual element))))
    (authority : writable = true → actual = .mutable ∧
      FreshWritableEvidence le first before owner ∧ FreshContentsEvidence le first before owner)
    (generated : GeneratedBuilderState before) (live : before.cur = some block)
    (floor : first ≤ before.vals.size)
    (run : eachElemValue slot byRef owner le before = (value, after)) :
    NewPermissionInstructions module func le first before after ∧
      PermissionTransfer le.mod.profile (FreshWritableEvidence le first after)
        (FreshContentsEvidence le first after) value localVar.ty := by
  cases byRef with
  | false =>
    simp only [Core.loopVarOk, Bool.false_eq_true, ite_false] at source
    have shape : localVar.ty = element := by
      by_cases same : (localVar.ty == element) = true
      · exact eq_of_beq same
      · simp [same, rej_ok] at source
    change emitDef (.load owner) le before = (value, after) at run
    refine ⟨newPermissions_free_emitDef (by trivial) run, ?_⟩
    rw [shape]
    cases element with
    | ref mu target =>
      cases mu with
      | readOnly => trivial
      | mutable =>
        have operation : (Op.load owner).resultTy (tyEnv le before) = .ok (.data (.ref .mutable target)) := by
          simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, typed,
            pure, Except.pure, bind, Except.bind]
        have recorded := (emitDef_recorded live operation).2.2.1
        change (emitDef (.load owner) le before).2.vals[(emitDef (.load owner) le before).1]? = _ at recorded
        rw [run] at recorded
        exact .mutable_reference
          ((freshWritableEvidence_load generated.dense generated.live live run recorded).weaken floor)
          ((freshContentsEvidence_intrinsic (.load owner) operation generated.dense generated.live live run).weaken floor)
    | _ => trivial
  | true =>
    cases destination : localVar.ty with
    | ref requested target =>
      simp only [Core.loopVarOk, ite_true, destination] at source
      have same : target = element := by
        by_cases equal : (target == element) = true
        · exact eq_of_beq equal
        · simp only [equal] at source
          obtain ⟨_, _, rejected, _⟩ := (st_bind_ok _ _ _ _).mp source
          exact ((rej_ok _ _ _ _).mp rejected).elim
      subst target
      simp only [eachElemValue, ite_true, bind_run, read_apply, row, destination] at run
      cases requested with
      | readOnly =>
        refine ⟨newPermissions_borrowTo typed ?_ generated run, ?_⟩
        · intro impossible; cases impossible
        · simp [PermissionTransfer]
      | mutable =>
        have allowed : writable = true := by
          cases writable with
          | true => rfl
          | false => simp [Core.requireWrite, rej_ok] at source
        obtain ⟨rfl, bindings, contents⟩ := authority allowed
        refine ⟨newPermissions_borrowTo typed (fun _ _ _ _ => contents) generated run, ?_⟩
        obtain ⟨binding, elements⟩ := borrowTo_mutable_reference_permissions bindings contents typed generated live run
        exact .mutable_reference binding elements
    | _ => simp [Core.loopVarOk, destination, rej_ok] at source

theorem eachSource_body_prefix_permissions
    {env : Core.TEnv} {view : View} {element : Ty} {writable byRef : Bool}
    {viewStart viewFinish : Nat}
    (source : Core.tyView env view viewStart = .ok ((element, writable), viewFinish))
    {slot : SlotId} {localVar : LocalVar} (row : env.vars[slot]? = some localVar)
    (binding : Core.loopVarOk localVar byRef element writable viewFinish = .ok ((), viewFinish))
    {results : List Ty} {module : GIR.Module} {func : Func} {first : Nat}
    {original sourceState input referenced after : LS}
    {sourceOwner : Option ValueId} {viewValue counter elementValue value : ValueId}
    (sourceRun : lowerEachSource view (lowerEnv env.mod env.vars results) original = ((sourceOwner, viewValue), sourceState))
    (originalGenerated : GeneratedBuilderState original) (sourceLive : sourceState.cur.isSome = true)
    (inputGenerated : GeneratedBuilderState input) (inputLive : input.cur.isSome = true)
    (floor : first ≤ original.vals.size)
    (extension : sourceState.Ext input) (grows : sourceState.vals.size ≤ input.vals.size)
    (types : TypePrefix sourceState input) (framed : TermEdgesFramed none sourceState input)
    (counterTyped : input.vals[counter]? = some (some (.data (.int .i64))))
    (referenceRun : emitDef (.refElem viewValue counter) (lowerEnv env.mod env.vars results) input = (elementValue, referenced))
    (valueRun : eachElemValue slot byRef elementValue (lowerEnv env.mod env.vars results) referenced = (value, after)) :
    NewPermissionInstructions module func (lowerEnv env.mod env.vars results) first input after ∧
      PermissionTransfer env.mod.profile (FreshWritableEvidence (lowerEnv env.mod env.vars results) first after)
        (FreshContentsEvidence (lowerEnv env.mod env.vars results) first after) value localVar.ty := by
  have viewRun := lowerEachSource_view_run view sourceRun
  have sourceGenerated := originalGenerated.lowerView view viewRun
  obtain ⟨actual, sourceTyped⟩ := lowerView_generated_typed view source viewRun sourceLive originalGenerated
  have inputTyped := types _ _ sourceTyped
  have operation : (Op.refElem viewValue counter).resultTy
      (tyEnv (lowerEnv env.mod env.vars results) input) = .ok (.data (.ref actual element)) := by
    simp [Op.resultTy, TyEnv.viewTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv,
      inputTyped, counterTyped, pure, Except.pure, bind, Except.bind]
  have sourceAuthority : writable = true → actual = .mutable ∧
      FreshContentsEvidence (lowerEnv env.mod env.vars results) first input viewValue := by
    intro permitted
    subst writable
    have mutableTyped := lowerView_generated_writable_typed view source viewRun sourceLive originalGenerated
    have same := Option.some.inj (Option.some.inj (sourceTyped.symm.trans mutableTyped))
    have mutable : actual = .mutable := (VTy.view.inj same).1
    have evidence := lowerEachSource_generated_contents view source sourceRun sourceLive originalGenerated
    exact ⟨mutable, (evidence.ext (loop := none) sourceGenerated.dense inputGenerated.dense
      extension grows types (by trivial) framed).weaken floor⟩
  cases current : input.cur with
  | none => simp [current] at inputLive
  | some block =>
    have elementTyped := (emitDef_recorded current operation).2.2.1
    change (emitDef (.refElem viewValue counter) (lowerEnv env.mod env.vars results) input).2.vals[
      (emitDef (.refElem viewValue counter) (lowerEnv env.mod env.vars results) input).1]? = _ at elementTyped
    rw [referenceRun] at elementTyped
    have preserved := (emitDef_recorded current operation).2.1
    change (emitDef (.refElem viewValue counter) (lowerEnv env.mod env.vars results) input).2.cur = input.cur at preserved
    rw [referenceRun] at preserved
    have referencedGenerated := inputGenerated.emitDef _ referenceRun
    have referencedLive : referenced.cur = some block := preserved.trans current
    have inputFloor := Nat.le_trans floor (Nat.le_trans (advB_lowerView view _ _ _ _ viewRun).vals grows)
    have referencedFloor := Nat.le_trans inputFloor (advB_emitDef _ _ _ _ _ referenceRun).vals
    have authority : writable = true → actual = .mutable ∧
        FreshWritableEvidence (lowerEnv env.mod env.vars results) first referenced elementValue ∧
        FreshContentsEvidence (lowerEnv env.mod env.vars results) first referenced elementValue := by
      intro permitted
      obtain ⟨mutable, evidence⟩ := sourceAuthority permitted
      exact ⟨mutable,
        evidence.emitDef_binding_dependency inputGenerated.dense inputGenerated.live current referenceRun
          (fun _ authorized => authorized),
        evidence.emitDef_dependency inputGenerated.dense inputGenerated.live current referenceRun
          (fun _ authorized => authorized)⟩
    have result := eachElemValue_permissionInstructions_transfer
      (le := lowerEnv env.mod env.vars results) (module := module) (func := func) (first := first)
      (by simpa only [lowerEnv] using row) binding elementTyped authority referencedGenerated referencedLive referencedFloor valueRun
    refine ⟨?_, result.2⟩
    exact (newPermissions_free_emitDef (module := module) (func := func) (first := first)
      (by trivial) referenceRun).compose_framed result.1 valueRun
      (dense_eachElemValue slot byRef elementValue) (advB_eachElemValue slot byRef elementValue)
      (types_eachElemValue slot byRef elementValue) (generatedTargetFrame_eachElemValue none slot byRef elementValue)
      referencedGenerated (by trivial)

#print axioms eachSource_body_prefix_permissions

#print axioms borrowTo_mutable_reference_permissions
#print axioms eachElemValue_permissionInstructions_transfer

end Goose.Lower.Validation
