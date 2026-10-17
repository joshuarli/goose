import Goose.Proofs.ConstructionExecutionProtocolDestination
import Goose.Proofs.ConstructionExecutionProtocolReservations
import Goose.Proofs.ConstructionExecutionProtocolCurrent

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

def receivingRenewal (snapshot : PendingDestination) (next : DestinationId) (writeEnd : Nat) : PendingDestination :=
  { snapshot with
    capability := { snapshot.capability with id := next }
    progress := .open 0
    writeEnd := writeEnd }

def receivingRenewalEvents (snapshot : PendingDestination) (next : DestinationId) :
    List ConstructionEvent :=
  match snapshot.backing with
  | .direct _ => [.begin next]
  | .staged _ _ => [.begin next, .stage next]

theorem DestinationResumptionsValid.lookup (state : ConstructionState)
    (valid : DestinationResumptionsValid state) (id : DestinationId)
    (snapshot : PendingDestination) (present : state.destinationResumptions.lookup id = some snapshot) :
    SavedDestinationBounds state id snapshot := by
  obtain ⟨before, after, rows, _⟩ := List.lookup_eq_some_iff.mp present
  apply valid (id, snapshot)
  simp [rows]

theorem receivingRenewal_allocate (state : ConstructionState) (id : DestinationId)
    (snapshot : PendingDestination) (writeEnd : Nat) (storage : Array ReceivingStorage)
    (size : storage.size = state.storage.size)
    (bounds : SavedDestinationBounds state id snapshot)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with
      destinations := state.destinations.push (receivingRenewal snapshot state.destinations.size writeEnd)
      storage := storage
      events := state.events ++ receivingRenewalEvents snapshot state.destinations.size } := by
  apply destinationLifecycleInvariant_push state _ _ storage size
  · rfl
  · exact bounds.writeStorage
  · exact bounds.receivingStorage
  · cases use : snapshot.use with
    | receiver => simp [receivingRenewal, use]
    | child parent | replacement parent =>
        have owner := bounds.owner
        simp only [use] at owner
        simpa only [receivingRenewal, use] using Nat.lt_trans owner bounds.allocated
  · intro index different
    cases backing : snapshot.backing <;>
      simp [receivingRenewalEvents, backing, destinationObservations, observeDestination,
        Ne.symm different]
  · cases backing : snapshot.backing with
    | direct storage =>
        refine ⟨.live false false, ?_, ?_⟩
        · simp [receivingRenewalEvents, backing, runDestinationTrace, destinationObservations,
            observeDestination, runDestinationObservations, destinationTraceStep]
        · cases use : snapshot.use <;>
            simp [receivingRenewal, backing, use, DestinationTracePhase.matchesDestination,
              DestinationTracePhase.matchesProgress]
    | staged receiver scratch =>
        refine ⟨.live true false, ?_, ?_⟩
        · simp [receivingRenewalEvents, backing, runDestinationTrace, destinationObservations,
            observeDestination, runDestinationObservations, destinationTraceStep]
        · cases use : snapshot.use <;>
            simp [receivingRenewal, backing, use, DestinationTracePhase.matchesDestination,
              DestinationTracePhase.matchesProgress]
  · exact valid

theorem receivingRenewal_allocate_owner (state : ConstructionState) (id parent : DestinationId)
    (snapshot before after : PendingDestination) (writeEnd : Nat) (storage : Array ReceivingStorage)
    (size : storage.size = state.storage.size)
    (bounds : SavedDestinationBounds state id snapshot)
    (present : state.destinations[parent]? = some before)
    (capability : after.capability.id = before.capability.id)
    (backing : after.backing = before.backing) (use : after.use = before.use)
    (transition : ∀ phase : DestinationTracePhase,
      phase.matchesDestination before → phase.matchesDestination after)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with
      destinations := (state.destinations.push (receivingRenewal snapshot state.destinations.size writeEnd)).set! parent after
      storage := storage
      events := state.events ++ receivingRenewalEvents snapshot state.destinations.size } := by
  let allocated : ConstructionState := { state with
    destinations := state.destinations.push (receivingRenewal snapshot state.destinations.size writeEnd)
    storage := storage
    events := state.events ++ receivingRenewalEvents snapshot state.destinations.size }
  have inside := (Array.getElem?_eq_some_iff.mp present).choose
  have allocatedValid : DestinationLifecycleInvariant allocated :=
    receivingRenewal_allocate state id snapshot writeEnd storage size bounds valid
  have parentPresent : allocated.destinations[parent]? = some before := by
    simpa only [allocated, Array.getElem?_push, Nat.ne_of_lt inside, ↓reduceIte] using present
  exact destinationLifecycleInvariant_replace_silent allocated parent before after storage parentPresent rfl
    capability backing use transition allocatedValid

#print axioms DestinationResumptionsValid.lookup
#print axioms receivingRenewal_allocate
#print axioms receivingRenewal_allocate_owner

end Goose.Proofs.ConstructionExecutionProtocol
