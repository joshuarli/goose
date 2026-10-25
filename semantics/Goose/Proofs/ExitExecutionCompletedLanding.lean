import Goose.Proofs.ExitExecutionLandingValues
import Goose.Proofs.ConstructionExecutionProtocolExitLanding
import Goose.Proofs.ConstructionExecutionOwnershipCleanup
import Lean

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionOwnership

open Lean Elab Term Meta in
elab "landing_source_head " declaration:ident : term => do
  let information ← getConstInfo declaration.getId
  forallTelescope information.type fun _ body => do
    unless body.isAppOf ``Eq do throwError "expected source operation equation"
    return body.getAppArgs[1]!.getAppFn

private abbrev sourceProtected : List PendingDestination → ConstructionM Unit :=
  landing_source_head Goose.Construct.protectedAbandonment_nil_transition

private theorem sourceProtected_eq (rows : List PendingDestination) :
    sourceProtected rows = protectedCleanup rows := by
  cases rows <;> rfl

open Lean Elab Term in
elab "landing_active_source" : term => do
  let information ← getConstInfo ``Goose.Construct.landCompletedReplacement_transition
  let some operation := information.type.find? (fun expression =>
    match expression with
    | .const name _ => name.toString.endsWith ".active"
    | _ => false) | throwError "expected native active destination predicate"
  return operation

private abbrev sourceActive : PendingDestination → Bool := landing_active_source

private theorem sourceActive_eq (row : PendingDestination) : sourceActive row = activeRow row := by
  cases row.progress <;> rfl

def landedReplacementRow (replacement superseded : PendingDestination) (count : Nat) : PendingDestination :=
  { replacement with
    capability := { replacement.capability with start := superseded.capability.start }
    use := superseded.use
    progress := .built count
    writeEnd := replacement.writeEnd - (replacement.capability.start - superseded.capability.start)
    rollbackEnd := superseded.rollbackEnd }

def completedLandingState (state : ConstructionState) (id old count : Nat)
    (replacement superseded : PendingDestination) (storage : ReceivingStorage)
    (parentUpdate : Option (DestinationId × PendingDestination)) : ConstructionState :=
  let cleaned := abandonRowsState (protectedRows state old id) state
  let landed := { cleaned with storage := cleaned.storage.set! replacement.storage (storage.landExit superseded.capability.start replacement.capability.start) }
  let adopted := { landed with destinations := landed.destinations.set! id (landedReplacementRow replacement superseded count) }
  let parented := match parentUpdate with
    | none => adopted
    | some (parentId, parent) => { adopted with destinations := adopted.destinations.set! parentId parent }
  if superseded.capability.start < replacement.capability.start then
    { parented with events := parented.events ++ [.relocate id .exitValue] }
  else parented

theorem completedStep_success (state : ConstructionState) (id old count : Nat)
    (replacement superseded : PendingDestination) (storage : ReceivingStorage)
    (parentUpdate : Option (DestinationId × PendingDestination))
    (indexed : DestinationCapabilitiesIndexed state)
    (present : state.destinations[id]? = some replacement)
    (stored : state.storage[replacement.storage]? = some storage)
    (ordered : superseded.capability.start ≤ replacement.capability.start)
    (inside : replacement.capability.start ≤ storage.bytes.size)
    (parentBound : ∀ parentId parent, parentUpdate = some (parentId, parent) → parentId < state.destinations.size) :
    completedStep id old count replacement superseded parentUpdate state =
      .ok () (completedLandingState state id old count replacement superseded storage parentUpdate) := by
  let rows := protectedRows state old id
  let cleaned := abandonRowsState rows state
  have bounded := (protectedRows_indexed state old id indexed).1
  have cleanFrame := abandonRowsState_frame rows state
  have cleanStorage : cleaned.storage[replacement.storage]? = some storage := by
    simpa only [cleaned, cleanFrame.1] using stored
  have destinationBound := (Array.getElem?_eq_some_iff.mp present).1
  have cleanBound : id < cleaned.destinations.size := by simpa only [cleaned, cleanFrame.2.2.1] using destinationBound
  have noBackward : ¬replacement.capability.start < superseded.capability.start := by omega
  simp only [completedStep, landCompletedReplacement_transition, lookupStorage_result, stored,
    bind, noBackward, ↓reduceIte, ConstructionM.get]
  simp only [sourceActive_eq]
  have cleanup : sourceProtected rows state = .ok () cleaned := by
    rw [sourceProtected_eq]
    exact protectedCleanup_exact rows state bounded
  conv at cleanup =>
    lhs
    simp only [sourceProtected, rows, protectedRows, destinationDescendant]
  rw [cleanup]
  simp only
  rw [landReceivingStorage_success cleaned replacement.storage storage superseded.capability.start replacement.capability.start cleanStorage ordered inside]
  simp only [replaceDestination_result, cleanBound, ↓reduceIte]
  cases update : parentUpdate with
  | none =>
    simp only
    split <;> rename_i moved <;>
      simp only [emit_result, completedLandingState, landedReplacementRow, cleaned, rows, moved, ↓reduceIte] <;> rfl
  | some pair =>
    obtain ⟨parentId, parent⟩ := pair
    have parentInside := parentBound parentId parent update
    have parentClean : parentId < cleaned.destinations.size := by
      simpa only [cleaned, cleanFrame.2.2.1] using parentInside
    simp only [Array.size_set!, parentClean, ↓reduceIte]
    split <;> rename_i moved <;>
      simp only [emit_result, completedLandingState, landedReplacementRow, cleaned, rows, moved, ↓reduceIte] <;> rfl

theorem completedLandingState_storage (state : ConstructionState) (id old count : Nat)
    (replacement superseded : PendingDestination) (storage : ReceivingStorage)
    (parentUpdate : Option (DestinationId × PendingDestination)) :
    (completedLandingState state id old count replacement superseded storage parentUpdate).storage =
      state.storage.set! replacement.storage (storage.landExit superseded.capability.start replacement.capability.start) := by
  have frame := (abandonRowsState_frame (protectedRows state old id) state).1
  cases parentUpdate <;> simp only [completedLandingState] <;> split <;> simpa only using congrArg
    (fun values => values.set! replacement.storage (storage.landExit superseded.capability.start replacement.capability.start)) frame

theorem completedLandingState_stdout (state : ConstructionState) (id old count : Nat)
    (replacement superseded : PendingDestination) (storage : ReceivingStorage)
    (parentUpdate : Option (DestinationId × PendingDestination)) :
    (completedLandingState state id old count replacement superseded storage parentUpdate).stdout = state.stdout := by
  have frame := (abandonRowsState_frame (protectedRows state old id) state).2.1
  cases parentUpdate <;> simp only [completedLandingState] <;> split <;> exact frame

theorem completedLandingState_outside_destination (state : ConstructionState) (id old count : Nat)
    (replacement superseded : PendingDestination) (storage : ReceivingStorage)
    (parentUpdate : Option (DestinationId × PendingDestination)) (outside : DestinationId)
    (different : id ≠ outside)
    (rows : ∀ row ∈ protectedRows state old id, row.capability.id ≠ outside)
    (parent : ∀ parentId row, parentUpdate = some (parentId, row) → parentId ≠ outside) :
    (completedLandingState state id old count replacement superseded storage parentUpdate).destinations[outside]? =
      state.destinations[outside]? := by
  have frame := abandonRowsState_outside (protectedRows state old id) state outside rows
  cases update : parentUpdate with
  | none =>
      simp only [completedLandingState]
      split <;> simpa only [Array.set!, Array.getElem?_setIfInBounds_ne different] using frame
  | some pair =>
      obtain ⟨parentId, row⟩ := pair
      have parentDifferent := parent parentId row update
      simp only [completedLandingState]
      split <;> simpa only [Array.set!, Array.getElem?_setIfInBounds_ne parentDifferent,
        Array.getElem?_setIfInBounds_ne different] using frame

theorem completedLandingState_replacement (state : ConstructionState) (id old count : Nat)
    (replacement superseded : PendingDestination) (storage : ReceivingStorage)
    (parentUpdate : Option (DestinationId × PendingDestination))
    (inside : id < state.destinations.size)
    (parent : ∀ parentId row, parentUpdate = some (parentId, row) → parentId ≠ id) :
    (completedLandingState state id old count replacement superseded storage parentUpdate).destinations[id]? =
      some (landedReplacementRow replacement superseded count) := by
  have size := (abandonRowsState_frame (protectedRows state old id) state).2.2.1
  have bound : id < (abandonRowsState (protectedRows state old id) state).destinations.size := by omega
  cases update : parentUpdate with
  | none =>
    simp only [completedLandingState]
    split <;> simp only [Array.set!, Array.getElem?_setIfInBounds_self_of_lt bound]
  | some pair =>
    obtain ⟨parentId, row⟩ := pair
    have parentDifferent := parent parentId row update
    simp only [completedLandingState]
    split <;> simp only [Array.set!, Array.getElem?_setIfInBounds_ne parentDifferent,
      Array.getElem?_setIfInBounds_self_of_lt bound]

theorem completedStep_missing_storage (state : ConstructionState) (id old count : Nat)
    (replacement superseded : PendingDestination)
    (parentUpdate : Option (DestinationId × PendingDestination))
    (missing : state.storage[replacement.storage]? = none) :
    completedStep id old count replacement superseded parentUpdate state = .fault .storage state := by
  simp only [completedStep, landCompletedReplacement_transition, lookupStorage_result, missing, bind]

theorem completedStep_backwards (state : ConstructionState) (id old count : Nat)
    (replacement superseded : PendingDestination) (storage : ReceivingStorage)
    (parentUpdate : Option (DestinationId × PendingDestination))
    (stored : state.storage[replacement.storage]? = some storage)
    (backwards : replacement.capability.start < superseded.capability.start) :
    completedStep id old count replacement superseded parentUpdate state = .fault .ownership state := by
  simp only [completedStep, landCompletedReplacement_transition, lookupStorage_result, stored, bind,
    backwards, ↓reduceIte, ConstructionM.fail]

theorem completedStep_payload_backing (fuel : Nat) (layout : LayoutEnv) (element : Goose.Construct.Ty)
    (length : Nat) (state : ConstructionState) (id old count : Nat)
    (replacement superseded : PendingDestination) (storage : ReceivingStorage)
    (parentUpdate : Option (DestinationId × PendingDestination)) (finish : Nat)
    (indexed : DestinationCapabilitiesIndexed state)
    (present : state.destinations[id]? = some replacement)
    (stored : state.storage[replacement.storage]? = some storage)
    (sameStorage : superseded.storage = replacement.storage)
    (ordered : superseded.capability.start ≤ replacement.capability.start)
    (backing : elementsEnd fuel layout element length storage.bytes replacement.capability.start = .ok finish)
    (inside : finish ≤ storage.bytes.size)
    (parentBound : ∀ parentId parent, parentUpdate = some (parentId, parent) → parentId < state.destinations.size)
    (parentDifferent : ∀ parentId parent, parentUpdate = some (parentId, parent) → parentId ≠ id) :
    ∃ after receiving,
      completedStep id old count replacement superseded parentUpdate state = .ok () after ∧
      after.stdout = state.stdout ∧
      after.destinations[id]? = some (landedReplacementRow replacement superseded count) ∧
      after.storage[superseded.storage]? = some receiving ∧
      elementsEnd fuel layout element length receiving.bytes superseded.capability.start =
        .ok (superseded.capability.start + (finish - replacement.capability.start)) := by
  have lower := elementsEnd_monotone fuel layout element length storage.bytes replacement.capability.start finish backing
  refine ⟨completedLandingState state id old count replacement superseded storage parentUpdate,
    storage.landExit superseded.capability.start replacement.capability.start,
    completedStep_success state id old count replacement superseded storage parentUpdate indexed present stored
      ordered (by omega) parentBound,
    completedLandingState_stdout state id old count replacement superseded storage parentUpdate,
    completedLandingState_replacement state id old count replacement superseded storage parentUpdate
      (Array.getElem?_eq_some_iff.mp present).1 parentDifferent, ?_, ?_⟩
  · rw [completedLandingState_storage, sameStorage]
    have bound := (Array.getElem?_eq_some_iff.mp stored).1
    simp only [Array.set!, Array.getElem?_setIfInBounds_self_of_lt bound]
  · exact landingBytes_elementsEnd fuel layout element length storage.bytes superseded.capability.start
      replacement.capability.start finish ordered backing inside

#print axioms completedStep_success
#print axioms completedLandingState_storage
#print axioms completedLandingState_stdout
#print axioms completedLandingState_outside_destination
#print axioms completedLandingState_replacement
#print axioms completedStep_missing_storage
#print axioms completedStep_backwards
#print axioms completedStep_payload_backing

end Goose.Proofs.ExitExecution
