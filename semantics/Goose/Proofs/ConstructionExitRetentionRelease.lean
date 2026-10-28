import Goose.Proofs.OwnershipAmbientContext
import Goose.Proofs.ConstructionExitCapturedRelease

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct

private theorem replacementSupported_ticket_release (state : ConstructionState) (token id : Nat)
    (supported : ReplacementSupported { state with exitReservations := state.exitReservations.set! token .released } id) :
    ReplacementSupported state id := by
  induction supported with
  | active id row present live => exact .active id row present live
  | parent id parent row present use supported ih => exact .parent id parent row present use ih

theorem retained_anchors_after_release (state : ConstructionState) (token : Nat)
    (carriers : List Carrier) (anchors : RetainedReplacementAnchors state carriers) :
    RetainedReplacementAnchors { state with exitReservations := state.exitReservations.set! token .released } carriers := by
  intro id row present inactive supported
  exact anchors id row present inactive (replacementSupported_ticket_release state token id supported)

private theorem fresh_ticket_before_release (state : ConstructionState) (released token incoming selected : Nat)
    (snapshot : PendingDestination)
    (present : (state.exitReservations.set! released .released)[token]? = some (.active .fresh incoming selected snapshot)) :
    state.exitReservations[token]? = some (.active .fresh incoming selected snapshot) := by
  by_cases same : token = released
  · subst token
    have inside := (Array.getElem?_eq_some_iff.mp present).1
    have releasedTicket : (state.exitReservations.set! released .released)[released]? = some .released := by
      rw [Array.set!_eq_setIfInBounds] at present ⊢
      exact Array.getElem?_setIfInBounds_self_of_lt (by simpa using inside)
    have impossible := present.symm.trans releasedTicket
    cases impossible
  · simpa [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, Ne.symm same] using present

theorem retained_boundaries_after_release (state : ConstructionState) (token : Nat)
    (ambient : OwnershipAmbient) (bounds : OwnershipAmbientBoundaries state ambient) :
    OwnershipAmbientBoundaries { state with exitReservations := state.exitReservations.set! token .released } ambient := by
  induction ambient with
  | nil => trivial
  | cons frame outer ih =>
    refine ⟨?_, ih bounds.2⟩
    intro index incoming reserved selected snapshot member ticket current retained carried
    have old := fresh_ticket_before_release state token index incoming reserved snapshot ticket
    have oldCurrent : destinationCurrent state reserved = .ok selected := by
      rw [destinationCurrent_congr_tables state
        { state with exitReservations := state.exitReservations.set! token .released } rfl rfl reserved] at current
      exact current
    exact bounds.1 index incoming reserved selected snapshot member old oldCurrent retained carried

theorem exit_retention_after_release (state : ConstructionState) (token : Nat) (channels : List Channel)
    (carriers : List Carrier) (outer : OwnershipAmbient)
    (valid : OwnershipAmbientInvariant state (.exitChannels [token] channels carriers :: outer)) :
    let after := { state with exitReservations := state.exitReservations.set! token .released }
    RetainedReplacementAnchors after (OwnershipAmbient.retained (.returned carriers :: outer)) ∧
      OwnershipAmbientBoundaries after (.returned carriers :: outer) := by
  have anchors := retained_anchors_after_release state token _ valid.anchors
  have bounds := retained_boundaries_after_release state token outer valid.boundaries.2
  constructor
  · simpa [OwnershipAmbient.retained, OwnershipAmbientFrame.carriers] using anchors
  · exact ⟨by simp [RetainedOutsideTickets, OwnershipAmbientFrame.tickets], bounds⟩

theorem exit_retention_cleanup (state : ExecutionState) (token incoming selected : Nat)
    (snapshot : PendingDestination) (channels : List Channel) (carriers : List Carrier)
    (outer : OwnershipAmbient) (origin : Goose.Core.OriginId)
    (ticket : state.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot))
    (valid : OwnershipAmbientInvariant state.construction (.exitChannels [token] channels carriers :: outer)) :
    ∃ after, Goose.Proofs.ExitExecution.exitChannelCleanupBorrowed origin [] [token] false carriers state = .ok () after ∧
      RetainedReplacementAnchors after.construction (OwnershipAmbient.retained (.returned carriers :: outer)) ∧
      OwnershipAmbientBoundaries after.construction (.returned carriers :: outer) := by
  let cleaned := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! token .released } }
  have released := releaseExitReservation_active state.construction token .fresh incoming selected snapshot ticket
  refine ⟨cleaned, ?_, exit_retention_after_release state.construction token channels carriers outer valid⟩
  simp only [Goose.Proofs.ExitExecution.exitChannelCleanupBorrowed, Bool.false_eq_true, ↓reduceIte,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.forIn_cons, List.forIn_nil,
    liftConstruction, released, bind, pure]
  rfl

theorem live_fresh_roles_after_release (state : ConstructionState) (token : Nat)
    (roles : LiveFreshReservationSuccessorRoles state) :
    LiveFreshReservationSuccessorRoles { state with exitReservations := state.exitReservations.set! token .released } := by
  intro index incoming reserved node snapshot selected ticket aliases present
  have old := fresh_ticket_before_release state token index incoming reserved snapshot ticket
  have oldAliases := DestinationSuccessorPath.congr
    (before := { state with exitReservations := state.exitReservations.set! token .released }) (after := state) rfl aliases
  exact roles index incoming reserved node snapshot selected old oldAliases present

#print axioms live_fresh_roles_after_release
#print axioms exit_retention_cleanup
#print axioms exit_retention_after_release
#print axioms retained_boundaries_after_release
#print axioms retained_anchors_after_release

end Goose.Proofs.ConstructionExecutionOwnership
