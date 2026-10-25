import Goose.Proofs.ConstructionExecutionProtocolNamedReservationMark
import Goose.Proofs.ConstructionExecutionProtocolReservationOwnerRestore

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

theorem namedReservation_replace_built_parent (state : ConstructionState) (selected : DestinationId)
    (parent : PendingDestination) (count : Nat)
    (present : state.destinations[selected]? = some parent)
    (mutable : SavedDestinationProgress parent.progress) (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant {state with destinations := state.destinations.set! selected {parent with progress := .built count}} := by
  constructor
  · apply destinationLifecycleInvariant_replace_silent state selected parent {parent with progress := .built count} state.storage present rfl rfl rfl rfl
    · intro phase matched
      cases phase with
      | live staged wrote => exact ⟨True.intro, True.intro⟩
      | unseen | published | abandoned =>
        have progressMatches := matched.1
        cases progress : parent.progress <;>
          simp_all only [SavedDestinationProgress, DestinationTracePhase.matchesProgress]
    · exact valid.1
  · apply destinationReservationStateValid_frame state _
    · apply reservationMetadataFrame_replace_progress state selected parent _ present
      intro stable
      cases progress : parent.progress <;> simp_all only [SavedDestinationProgress, ReservationStableProgress]
    · exact valid.2

theorem namedReservation_replace_direct_ticket (state : ConstructionState) (token : ExitReservationId)
    (role : ExitReservationRole) (incoming selected : DestinationId) (snapshot : PendingDestination)
    (present : state.destinations[selected]? = some snapshot) (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant {state with
      exitReservations := state.exitReservations.set! token (.active role incoming selected snapshot)} := by
  by_cases inside : token < state.exitReservations.size
  · constructor
    · exact valid.1
    · have correct := valid.1.2.1 selected snapshot present
      have bounds := savedDestinationBounds_of_row state selected snapshot present valid.1
      apply destinationReservationStateValid_replace_direct state token role incoming selected snapshot inside
      · simpa only [correct] using bounds
      · exact correct
      · exact valid.2
  · have outside : state.exitReservations.size ≤ token := Nat.le_of_not_gt inside
    simpa only [Array.set!_eq_setIfInBounds, Array.setIfInBounds_eq_of_size_le outside] using valid

abbrev namedReservationReadStorage (id : StorageId) : ConstructionM ReceivingStorage := fun state =>
  (fun {left right : ConstructionResult ReceivingStorage} (_ : left = right) => left)
    (lookupStorage_result id state)

abbrev namedReservationWriteDestination (id : DestinationId) (snapshot : PendingDestination) : ConstructionM Unit := fun state =>
  (fun {left right : ConstructionResult Unit} (_ : left = right) => left)
    (replaceDestination_result id snapshot state)

def namedReservationFinish (token : ExitReservationId) (incoming selected : DestinationId)
    (snapshot : PendingDestination) : ConstructionM DestinationId := do
  let storage ← namedReservationReadStorage snapshot.storage
  if snapshot.writeEnd > storage.bytes.size then ConstructionM.fail .ownership
  namedReservationWriteDestination selected snapshot
  let state ← ConstructionM.get
  ConstructionM.set {state with
    exitReservations := state.exitReservations.set! token (.active (.named .materialized) incoming selected snapshot)}
  pure selected

theorem namedReservationFinish_lifecycle (token : ExitReservationId) (incoming selected : DestinationId)
    (snapshot parent : PendingDestination) (count : Nat) (state : ConstructionState)
    (present : state.destinations[selected]? = some parent)
    (normalized : {parent with progress := .built count} = snapshot)
    (mutable : SavedDestinationProgress parent.progress) (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant (namedReservationFinish token incoming selected snapshot state).finalState := by
  have restored : ReservationLifecycleInvariant {state with destinations := state.destinations.set! selected snapshot} := by
    rw [← normalized]
    exact namedReservation_replace_built_parent state selected parent count present mutable valid
  have inside := (Array.getElem?_eq_some_iff.mp present).choose
  have ticket := namedReservation_replace_direct_ticket
    {state with destinations := state.destinations.set! selected snapshot} token (.named .materialized) incoming selected snapshot
    (by simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt inside]) restored
  simp only [namedReservationFinish, namedReservationReadStorage, lookupStorage_result, bind]
  cases stored : state.storage[snapshot.storage]? with
  | none => exact valid
  | some storage =>
    simp only [stored]
    split
    · exact valid
    · simpa only [namedReservationWriteDestination, replaceDestination_result, inside, ↓reduceIte,
        ConstructionM.get, ConstructionM.set, bind, pure, ConstructionResult.finalState] using ticket

end Goose.Proofs.ConstructionExecutionProtocol
