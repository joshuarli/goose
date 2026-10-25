import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsLandingRows
import Goose.Proofs.ConstructionExecutionProtocolExitLanding

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

private abbrev lookupStorage (id : StorageId) : ConstructionM ReceivingStorage := fun state =>
  (fun {left right : ConstructionResult ReceivingStorage} (_ : left = right) => left) (lookupStorage_result id state)

private abbrev replaceDestination (id : DestinationId) (row : PendingDestination) : ConstructionM Unit := fun state =>
  (fun {left right : ConstructionResult Unit} (_ : left = right) => left) (replaceDestination_result id row state)

private abbrev emit (event : ConstructionEvent) : ConstructionM Unit := fun state =>
  (fun {left right : ConstructionResult Unit} (_ : left = right) => left) (emit_result event state)

private def landingUpdates (id count : Nat) (replacement superseded : PendingDestination)
    (parentUpdate : Option (DestinationId × PendingDestination)) : ConstructionM Unit := do
  replaceDestination id { replacement with
    capability := { replacement.capability with start := superseded.capability.start }
    use := superseded.use
    progress := .built count
    writeEnd := replacement.writeEnd - (replacement.capability.start - superseded.capability.start)
    rollbackEnd := superseded.rollbackEnd }
  if let some (parentId, parent) := parentUpdate then replaceDestination parentId parent
  if superseded.capability.start < replacement.capability.start then emit (.relocate id .exitValue)

private def completedFlow (id old count : Nat) (replacement superseded : PendingDestination)
    (parentUpdate : Option (DestinationId × PendingDestination)) : ConstructionM Unit := do
  let _ ← lookupStorage replacement.storage
  if replacement.capability.start < superseded.capability.start then ConstructionM.fail .ownership
  let state ← ConstructionM.get
  protectedCleanup (protectedRows state old id)
  landReceivingStorage replacement.storage superseded.capability.start replacement.capability.start
  landingUpdates id count replacement superseded parentUpdate

private theorem completedStep_flow (id old count : Nat) (replacement superseded : PendingDestination)
    (parentUpdate : Option (DestinationId × PendingDestination)) :
    completedStep id old count replacement superseded parentUpdate =
      completedFlow id old count replacement superseded parentUpdate := by
  funext state
  simp only [completedStep, landCompletedReplacement_transition, completedFlow, landingUpdates, lookupStorage, lookupStorage_result, bind]
  cases stored : state.storage[replacement.storage]? with
  | none => rfl
  | some storage =>
      simp only [stored, pure, bind]
      by_cases backwards : replacement.capability.start < superseded.capability.start
      · simp only [backwards, ↓reduceIte, ConstructionM.fail, bind]
      · simp only [backwards, ↓reduceIte, ConstructionM.get, bind]
        change ((_ : List PendingDestination → ConstructionM Unit) (protectedRows state old id) >>= _) state =
          (protectedCleanup (protectedRows state old id) >>= _) state
        cases rowsEq : protectedRows state old id <;> cases parentUpdate
        all_goals simp only [rowsEq, protectedCleanup, replaceDestination, emit, bind]

def ownershipLandedRow (count : Nat) (replacement anchor : PendingDestination) : PendingDestination :=
  { replacement with
    capability := {replacement.capability with start := anchor.capability.start}
    use := anchor.use
    progress := .built count
    writeEnd := replacement.writeEnd - (replacement.capability.start - anchor.capability.start)
    rollbackEnd := anchor.rollbackEnd }

private theorem landingUpdates_table (state : ConstructionState) (id count : Nat)
    (replacement anchor : PendingDestination) (update : Option (DestinationId × PendingDestination))
    (inside : id < state.destinations.size)
    (parents : ∀ parent updated, update = some (parent, updated) → parent < state.destinations.size) :
    (landingUpdates id count replacement anchor update state).finalState.destinations =
      match update with
      | none => state.destinations.set! id (ownershipLandedRow count replacement anchor)
      | some (parent, updated) => (state.destinations.set! id (ownershipLandedRow count replacement anchor)).set! parent updated := by
  cases update with
  | none =>
      by_cases relocate : anchor.capability.start < replacement.capability.start <;>
        simp [landingUpdates, replaceDestination, replaceDestination_result, emit, emit_result,
          ownershipLandedRow, inside, relocate, bind, pure, ConstructionResult.finalState]
  | some pair =>
      obtain ⟨parent, updated⟩ := pair
      have parentInside := parents parent updated rfl
      by_cases relocate : anchor.capability.start < replacement.capability.start <;>
        simp [landingUpdates, replaceDestination, replaceDestination_result, emit, emit_result,
          ownershipLandedRow, inside, parentInside, relocate, bind, pure, ConstructionResult.finalState]

private theorem receiving_table (storage start payload : Nat) (state : ConstructionState) :
    (landReceivingStorage storage start payload state).finalState.destinations = state.destinations := by
  unfold landReceivingStorage
  cases found : state.storage[storage]? with
  | none => rfl
  | some row => simp only; split <;> rfl

theorem completedStep_ownership_tables (state : ConstructionState) (id root count : Nat)
    (replacement anchor : PendingDestination) (update : Option (DestinationId × PendingDestination))
    (valid : DestinationLifecycleInvariant state) (earlier : root < id)
    (present : state.destinations[id]? = some replacement)
    (anchorPresent : state.destinations[root]? = some anchor)
    (choice : OwnershipLandingParentChoice state root id anchor update) :
    let table := (completedStep id root count replacement anchor update state).finalState.destinations
    table = state.destinations ∨
      table = (abandonRowsState (protectedRows state root id) state).destinations ∨
      table = (protectedCleanupRewireState state root id (ownershipLandedRow count replacement anchor) update).destinations := by
  rw [completedStep_flow]
  simp only [completedFlow, lookupStorage, lookupStorage_result, bind]
  cases stored : state.storage[replacement.storage]? with
  | none => exact Or.inl rfl
  | some storage =>
      simp only [stored, pure, bind]
      by_cases backwards : replacement.capability.start < anchor.capability.start
      · simp only [backwards, ↓reduceIte, ConstructionM.fail, bind, ConstructionResult.finalState]
        exact Or.inl (by trivial)
      · simp only [backwards, ↓reduceIte, ConstructionM.get, pure, bind]
        let cleaned := abandonRowsState (protectedRows state root id) state
        have size : cleaned.destinations.size = state.destinations.size := (abandonRowsState_frame _ state).2.2.1
        rw [protectedCleanup_exact _ state (protectedRows_indexed state root id valid.2.1).1]
        simp only [bind]
        have receivedFrame := receiving_table replacement.storage anchor.capability.start replacement.capability.start cleaned
        cases received : landReceivingStorage replacement.storage anchor.capability.start replacement.capability.start cleaned with
        | fault reason after =>
            simp only [received, ConstructionResult.finalState] at receivedFrame
            exact Or.inr (Or.inl receivedFrame)
        | ok value after =>
            simp only [received, ConstructionResult.finalState] at receivedFrame
            simp only [bind]
            apply Or.inr ∘ Or.inr
            have finalInside : id < after.destinations.size := by
              rw [receivedFrame, size]
              exact (Array.getElem?_eq_some_iff.mp present).1
            have parentsInside : ∀ parent updated, update = some (parent, updated) → parent < after.destinations.size := by
              intro parent updated selected
              obtain ⟨row, found, _, _⟩ := ownershipLandingParentChoice_parent state root id anchor update
                valid.2.2.2 anchorPresent choice parent updated selected
              rw [receivedFrame, size]
              exact (Array.getElem?_eq_some_iff.mp found).1
            rw [landingUpdates_table after id count replacement anchor update finalInside parentsInside]
            cases update <;> simp only [protectedCleanupRewireState, receivedFrame, cleaned]

end Goose.Proofs.ConstructionExecutionOwnership
