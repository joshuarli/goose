import Goose.Proofs.ConstructionExecutionOwnershipCleanup

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

def SameDestinationIdentity (before after : PendingDestination) : Prop :=
  after.capability.id = before.capability.id ∧
  after.capability.receiver = before.capability.receiver ∧
  after.capability.layout = before.capability.layout ∧
  after.capability.request = before.capability.request ∧
  after.capability.start = before.capability.start ∧
  after.capability.owner = before.capability.owner ∧
  after.backing = before.backing ∧ after.use = before.use ∧ after.progress = before.progress

theorem sameDestinationIdentity_refl (destination : PendingDestination) :
    SameDestinationIdentity destination destination := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 1000000 in
theorem prepareNamedBinding_identity (state : ConstructionState) (id : DestinationId)
    (before : PendingDestination) (localType : Construct.Ty)
    (present : state.destinations[id]? = some before) :
    ∃ after, (prepareNamedBinding id localType state).finalState.destinations[id]? = some after ∧
      SameDestinationIdentity before after ∧
      (prepareNamedBinding id localType state).finalState.destinations.size = state.destinations.size ∧
      (prepareNamedBinding id localType state).finalState.events = state.events := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  simp only [prepareNamedBinding, writableDestination_result, present, bind]
  cases writable : destinationCanWrite state id with
  | false => exact ⟨before, present, sameDestinationIdentity_refl before, rfl, rfl⟩
  | true =>
      simp only [writable]
      cases progress : before.progress <;> try simp only [progress] <;>
        try exact ⟨before, present, sameDestinationIdentity_refl before, rfl, rfl⟩
      case «open» count =>
        cases count with
        | succ count => exact ⟨before, present, sameDestinationIdentity_refl before, rfl, rfl⟩
        | zero =>
            simp only [pure, bind]
            split
            · exact ⟨before, present, sameDestinationIdentity_refl before, rfl, rfl⟩
            · simp only [lookupStorage_result, bind]
              cases stored : state.storage[before.storage]? with
              | none => exact ⟨before, present, sameDestinationIdentity_refl before, rfl, rfl⟩
              | some storage =>
                  simp only [stored, bind]
                  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
                  cases localType <;> cases layoutFound : before.layout <;>
                    by_cases endSame : before.writeEnd = before.capability.start <;>
                    simp_all [layoutFound, endSame, replaceStorage_result, replaceDestination_result,
                      bind, storageInside, inside, pure, ConstructionM.fail, ConstructionResult.finalState,
                      SameDestinationIdentity]

theorem prepareNamedBinding_no_delivery_events (state : ConstructionState) (id : DestinationId)
    (before : PendingDestination) (localType : Construct.Ty)
    (present : state.destinations[id]? = some before) :
    (prepareNamedBinding id localType state).finalState.events = state.events := by
  obtain ⟨after, found, identity, size, events⟩ := prepareNamedBinding_identity state id before localType present
  exact events

end Goose.Proofs.ConstructionExecutionOwnership
