import Goose.Proofs.OwnershipAmbientTicketScopes
import Goose.Proofs.ConstructionExecutionOwnershipReservations
import Goose.Proofs.ExitExecutionBase

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct

theorem release_single_exit_frame (state : ConstructionState) (token incoming selected : Nat)
    (snapshot : PendingDestination) (channels : List Channel) (carriers : List Carrier)
    (outer : OwnershipAmbient)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming selected snapshot))
    (frames : OwnershipReservationFrames state (.exitChannels [token] channels carriers :: outer)) :
    ∃ after, releaseExitReservation token state = .ok () after ∧
      OwnershipFrameReleased after (.exitChannels [token] channels carriers) ∧
      OwnershipReservationFrames after outer := by
  let after := { state with exitReservations := state.exitReservations.set! token .released }
  have inside := (Array.getElem?_eq_some_iff.mp ticket).1
  have released : after.exitReservations[token]? = some .released := by
    simp only [after, Array.set!_eq_setIfInBounds]
    exact Array.getElem?_setIfInBounds_self_of_lt inside
  have allFrames : OwnershipReservationFrames after (.exitChannels [token] channels carriers :: outer) := by
    apply ownershipReservationFrames_ticket_preimage state after _ _ frames
    intro other reservation found live
    by_cases same : other = token
    · subst other
      have equal : reservation = .released := Option.some.inj (found.symm.trans released)
      subst reservation
      exact False.elim live
    · have old : state.exitReservations[other]? = some reservation := by
        simpa [after, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, Ne.symm same] using found
      exact ⟨reservation, old, live⟩
  have frameReleased : OwnershipFrameReleased after (.exitChannels [token] channels carriers) := by
    intro other member
    simp only [OwnershipAmbientFrame.tickets, List.mem_singleton] at member
    subst other
    exact released
  exact ⟨after, releaseExitReservation_active state token .fresh incoming selected snapshot ticket,
    frameReleased, ownershipReservationFrames_pop_released after _ outer allFrames frameReleased⟩

theorem cleanup_single_exit_frame (state : ExecutionState) (token incoming selected : Nat)
    (snapshot : PendingDestination) (channels : List Channel) (carriers : List Carrier)
    (outer : OwnershipAmbient) (origin : Goose.Core.OriginId)
    (ticket : state.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot))
    (frames : OwnershipReservationFrames state.construction (.exitChannels [token] channels carriers :: outer)) :
    ∃ after, Goose.Proofs.ExitExecution.exitChannelCleanupBorrowed origin [] [token] false carriers state = .ok () after ∧
      OwnershipFrameReleased after.construction (.exitChannels [token] channels carriers) ∧
      OwnershipReservationFrames after.construction outer := by
  obtain ⟨after, released, discharged, popped⟩ := release_single_exit_frame state.construction token incoming selected snapshot
    channels carriers outer ticket frames
  refine ⟨{ state with construction := after }, ?_, discharged, popped⟩
  simp only [Goose.Proofs.ExitExecution.exitChannelCleanupBorrowed, Bool.false_eq_true, ↓reduceIte,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.forIn_cons, List.forIn_nil,
    liftConstruction, released, bind, pure]

#print axioms cleanup_single_exit_frame
#print axioms release_single_exit_frame

end Goose.Proofs.ConstructionExecutionOwnership
