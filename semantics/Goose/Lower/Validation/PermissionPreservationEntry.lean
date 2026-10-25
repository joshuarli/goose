import Goose.Lower.Validation.PermissionPreservationFinishing
import Goose.Lower.Validation.PermissionPreservationEntryParameters
import Goose.Lower.Validation.PermissionPreservationSourceTables
import Goose.Core.Sound.Module
import Goose.Lower.Validation.ValidationTypedModuleTables

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem implementation_body_returnTransfers
    {module : Core.Module} {impl : Core.Impl} (checked : ImplOk module impl)
    {func : Func} (results : func.results = impl.results.toList)
    {pre : List (SlotId × ValueId × OriginId)} {before after : LS} {value : ValueId}
    (run : lowerBlock none pre false impl.body (lowerEnv module impl.vars impl.results.toList) before = (value, after))
    (generated : GeneratedBuilderState before) (live : after.cur.isSome = true) :
    ∀ entry ∈ func.results.zip (if impl.body.value.isSome then [value] else []),
      PermissionTransfer module.profile
        (FreshWritableEvidence (lowerEnv module impl.vars impl.results.toList) 0 after)
        (FreshContentsEvidence (lowerEnv module impl.vars impl.results.toList) 0 after) entry.2 entry.1 := by
  obtain ⟨bodyType, finish, source, shape⟩ := checked.body
  cases bodyEq : impl.body with
  | mk scope statements expression =>
    cases expression with
    | none =>
      intro entry member
      simp [Core.Block.value] at member
    | some expr =>
      rcases shape with ⟨empty, _⟩ | ⟨target, outputs, typed, _⟩
      · intro entry member
        rw [results, empty] at member
        simp at member
      · have sameType : bodyType = target := typed (by simp [bodyEq, Core.Block.value])
        subst bodyType
        rw [bodyEq] at source run
        have allowed := lowerBlock_value_permissionTransfer source (permissionStorage_passable_self target)
          run generated (by trivial) live
        intro entry member
        have sameEntry : entry = (target, value) := by
          simpa [results, outputs, bodyEq, Core.Block.value] using member
        subst entry
        exact allowed

theorem implementation_permission_state_of_body
    {module : Core.Module} {impl : Core.Impl} (checked : ImplOk module impl)
    {func : Func} (slots : func.slots = (lowerEnv module impl.vars impl.results.toList).slots)
    (results : func.results = impl.results.toList)
    (bodyPermissions : ∀ {pre : List (SlotId × ValueId × OriginId)} {before after : LS} {value : ValueId},
      GeneratedBuilderState before →
      (∀ entry ∈ pre, ∀ descriptor, func.slots[entry.1]? = some descriptor →
        PermissionTransfer module.profile
          (FreshWritableEvidence (lowerEnv module impl.vars impl.results.toList) 0 before)
          (FreshContentsEvidence (lowerEnv module impl.vars impl.results.toList) 0 before) entry.2.1 descriptor.ty) →
      lowerBlock none pre false impl.body (lowerEnv module impl.vars impl.results.toList) before = (value, after) →
      NewPermissionInstructions (lower module) func (lowerEnv module impl.vars impl.results.toList) 0 before after) :
    PermissionState (lower module) func (lowerEnv module impl.vars impl.results.toList)
      (cfg_implState module impl) := by
  let le := lowerEnv module impl.vars impl.results.toList
  let types := impl.params.toList.map fun parameter => VTy.data (tyOfVar impl parameter.var)
  let allocated := newBlock types le initState
  let entered := setCur (some allocated.1.1) le allocated.2
  let pre := (impl.params.toList.zip allocated.1.2).map fun (parameter, value) =>
    (parameter.var, value, (impl.vars[parameter.var]?.map (fun localVar : LocalVar => localVar.org)).getD 0)
  let bodyResult := lowerBlock none pre false impl.body le entered.2
  let finished := finishFunction impl bodyResult.1 le bodyResult.2
  have allocatedRun : newBlock types le initState = allocated := rfl
  have enteredRun : setCur (some allocated.1.1) le allocated.2 = entered := rfl
  have bodyRun : lowerBlock none pre false impl.body le entered.2 = bodyResult := rfl
  have finishedRun : finishFunction impl bodyResult.1 le bodyResult.2 = finished := rfl
  have allocatedGenerated := GeneratedBuilderState.initState.newBlock types allocatedRun
  have entryBound : allocated.1.1 < allocated.2.blocks.size := by
    simp [allocated, newBlock_run_general, initState]
  have enteredGenerated := allocatedGenerated.setCur (some allocated.1.1)
    (by intro actual same; cases same; exact entryBound) enteredRun
  have preTransfer : ∀ entry ∈ pre, ∀ descriptor, func.slots[entry.1]? = some descriptor →
      PermissionTransfer module.profile (FreshWritableEvidence le 0 entered.2)
        (FreshContentsEvidence le 0 entered.2) entry.2.1 descriptor.ty := by
    intro entry member descriptor row
    have allowed := newBlock_implementation_preTransfers slots allocatedRun entry member descriptor row
    exact allowed
  have bodyIssued := bodyPermissions enteredGenerated preTransfer bodyRun
  have bodyGenerated := enteredGenerated.lowerBlock none pre false impl.body trivial bodyRun
  have finishedIssued := newPermissions_finishFunction (module := lower module) (func := func) (first := 0) finishedRun bodyGenerated (fun live =>
    implementation_body_returnTransfers checked results bodyRun enteredGenerated live)
  have issued := bodyIssued.compose_framed finishedIssued finishedRun (dense_finishFunction impl bodyResult.1)
    (advB_finishFunction impl bodyResult.1) (permission_types_finishFunction impl bodyResult.1)
    (permission_frame_finishFunction none impl bodyResult.1) bodyGenerated trivial
  have original := (issued.prepend_setCur enteredRun).prepend_newBlock allocatedRun
  change PermissionState (lower module) func le finished.2
  exact original.finish (by intro instruction member; simp [Goose.Lower.initState, LS.insts] at member)

theorem global_permission_state_of_expression
    {module : Core.Module} {global : Core.Global} {index finish : Nat}
    (source : Core.tyExpr (initEnv module index) global.init 0 = .ok (global.ty, finish))
    {func : Func} (results : func.results = [global.ty])
    (childPermissions : ∀ {before after : LS} {value : ValueId}, GeneratedBuilderState before →
      lowerExpr global.init (lowerEnv module #[] [global.ty]) before = (value, after) →
      NewPermissionInstructions (lower module) func (lowerEnv module #[] [global.ty]) before.vals.size before after) :
    PermissionState (lower module) func (lowerEnv module #[] [global.ty]) (cfg_globalState module global) := by
  let le := lowerEnv module #[] [global.ty]
  let allocated := newBlock [] le initState
  let entered := setCur (some allocated.1.1) le allocated.2
  let evaluated := lowerExpr global.init le entered.2
  let returned := emitTerm (.ret [evaluated.1] (some global.org)) le evaluated.2
  have allocatedRun : newBlock [] le initState = allocated := rfl
  have enteredRun : setCur (some allocated.1.1) le allocated.2 = entered := rfl
  have expressionRun : lowerExpr global.init le entered.2 = evaluated := rfl
  have returnedRun : emitTerm (.ret [evaluated.1] (some global.org)) le evaluated.2 = returned := rfl
  have allocatedGenerated := GeneratedBuilderState.initState.newBlock [] allocatedRun
  have entryBound : allocated.1.1 < allocated.2.blocks.size := by
    simp [allocated, newBlock_run_general, initState]
  have enteredGenerated := allocatedGenerated.setCur (some allocated.1.1)
    (by intro actual same; cases same; exact entryBound) enteredRun
  have evaluatedGenerated := enteredGenerated.lowerExpr global.init expressionRun
  have head := (childPermissions enteredGenerated expressionRun).weaken (Nat.zero_le _)
  have tail := NewPermissionInstructions.emitTerm (module := lower module) (func := func) (first := 0)
    returnedRun (fun live => .ret (fun entry member => by
      have same : entry = (global.ty, evaluated.1) := by simpa [results] using member
      subst entry
      have allowed := lowerExpr_generated_permissionTransfer global.init source
        (permissionStorage_passable_self global.ty) expressionRun live enteredGenerated
      exact (allowed.fresh_weaken (Nat.zero_le _)).fresh_of_framed_run returnedRun (dense_emitTerm _)
        (advB_emitTerm _) (types_emitTerm _)
        (generatedTargetFrame_emitNoSuccessors none _ (by simp [Term.successors])) evaluatedGenerated trivial))
  have issued := head.compose_framed tail returnedRun (dense_emitTerm _) (advB_emitTerm _) (types_emitTerm _)
    (generatedTargetFrame_emitNoSuccessors none _ (by simp [Term.successors])) evaluatedGenerated trivial
  have original := (issued.prepend_setCur enteredRun).prepend_newBlock allocatedRun
  change PermissionState (lower module) func le returned.2
  exact original.finish (by intro instruction member; simp [Goose.Lower.initState, LS.insts] at member)

theorem implementation_permission_check_of_state
    {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : ImplId} {impl : Core.Impl} (row : module.impls[index]? = some impl)
    (permitted : PermissionState (lower module) (lowerImpl module impl)
      (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)) (label : String) :
    checkPermissions (lower module) label (lowerImpl module impl)
      ((lowerImpl module impl).valueTypes (lower module)) = .ok () :=
  permitted.check_reconstructed (cfg_impl_blocks module impl) rfl
    (lowerImpl_valueTypes_of_accepted accepted row) label

theorem context_permission_check_of_state
    {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : ImplId} {impl : Core.Impl} (row : module.impls[index]? = some impl) (context : Context)
    (permitted : PermissionState (lower module) (lowerContextAt module context impl)
      (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)) (label : String) :
    checkPermissions (lower module) label (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module)) = .ok () :=
  permitted.check_reconstructed (cfg_context_blocks module context impl) rfl
    (lowerContext_valueTypes_of_accepted accepted row) label

theorem global_permission_check_of_state
    {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : GlobalId} {global : Core.Global} (row : module.globals[index]? = some global)
    (permitted : PermissionState (lower module) (lowerGlobal module global).init
      (lowerEnv module #[] [global.ty]) (cfg_globalState module global)) (label : String) :
    checkPermissions (lower module) label (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module)) = .ok () :=
  permitted.check_reconstructed (cfg_global_blocks module global) rfl
    (lowerGlobal_valueTypes_of_accepted accepted row) label

#print axioms implementation_permission_check_of_state
#print axioms context_permission_check_of_state
#print axioms global_permission_check_of_state

#print axioms global_permission_state_of_expression

#print axioms implementation_permission_state_of_body

#print axioms implementation_body_returnTransfers

end Goose.Lower.Validation
