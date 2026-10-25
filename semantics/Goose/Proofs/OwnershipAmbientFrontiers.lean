import Goose.Proofs.OwnershipAmbientContext

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

theorem completedCarrierIds_append (first second : List Construct.Carrier) :
    completedCarrierIds (first ++ second) = completedCarrierIds first ++ completedCarrierIds second := by
  simp [completedCarrierIds, List.filterMap_append]

theorem retainedOutsideTickets_nil (state : ConstructionState) (carriers : List Construct.Carrier) :
    RetainedOutsideTickets state [] carriers := by
  intro token incoming reserved selected snapshot member
  simp at member

theorem ownershipAmbientInvariant_reemit_head (state : ConstructionState)
    (frame : OwnershipAmbientFrame) (outer : OwnershipAmbient)
    (valid : OwnershipAmbientInvariant state (frame :: outer)) :
    OwnershipAmbientInvariant state (.returned frame.carriers :: outer) := by
  refine ⟨valid.structural, ?_, ⟨retainedOutsideTickets_nil state _, valid.boundaries.2⟩⟩
  simpa only [OwnershipAmbient.retained, List.flatMap_cons, OwnershipAmbientFrame.carriers] using valid.anchors

theorem ownershipAmbientInvariant_returned_nil (state : ConstructionState) (ambient : OwnershipAmbient) :
    OwnershipAmbientInvariant state (.returned [] :: ambient) ↔ OwnershipAmbientInvariant state ambient := by
  constructor
  · intro valid
    refine ⟨valid.structural, ?_, valid.boundaries.2⟩
    simpa [OwnershipAmbient.retained, OwnershipAmbientFrame.carriers] using valid.anchors
  · intro valid
    refine ⟨valid.structural, ?_, ⟨retainedOutsideTickets_nil state _, valid.boundaries⟩⟩
    simpa [OwnershipAmbient.retained, OwnershipAmbientFrame.carriers] using valid.anchors

theorem ownershipAmbientInvariant_capture_returned (state : ConstructionState)
    (frame : OwnershipAmbientFrame) (outer : OwnershipAmbient) (carriers : List Construct.Carrier) :
    OwnershipAmbientInvariant state (.returned carriers :: frame.withCarriers [] :: outer) ↔
      OwnershipAmbientInvariant state (frame.withCarriers carriers :: outer) := by
  cases frame <;>
    constructor
  all_goals
    intro valid
    refine ⟨valid.structural, ?_, ?_⟩
    · simpa [OwnershipAmbient.retained, OwnershipAmbientFrame.withCarriers,
        OwnershipAmbientFrame.carriers, List.append_assoc] using valid.anchors
    · simpa [OwnershipAmbientBoundaries, OwnershipAmbientFrame.withCarriers,
        OwnershipAmbientFrame.tickets, RetainedOutsideTickets] using valid.boundaries

theorem ownershipAmbient_selected_frontier (state : ConstructionState)
    (frame : OwnershipAmbientFrame) (outer : OwnershipAmbient)
    (valid : OwnershipAmbientInvariant state (frame :: outer))
    (token : ExitReservationId) (incoming reserved selected : DestinationId)
    (snapshot destination : PendingDestination)
    (owned : token ∈ frame.tickets)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (current : destinationCurrent state reserved = .ok selected)
    (present : state.destinations[selected]? = some destination)
    (inactive : activeProgress destination.progress = false)
    (supported : ReplacementSupported state selected) :
    CarriedReservationBranch state selected (completedCarrierIds frame.carriers) := by
  obtain ⟨retained, member, descendant⟩ := valid.anchors selected destination present inactive supported
  have membership : retained ∈ completedCarrierIds frame.carriers ∨
      retained ∈ completedCarrierIds (OwnershipAmbient.retained outer) := by
    simpa only [OwnershipAmbient.retained, List.flatMap_cons, completedCarrierIds_append,
      List.mem_append] using member
  rcases membership with own | ambient
  · exact List.any_eq_true.mpr ⟨retained, own, descendant⟩
  · have excluded := valid.boundaries.1 token incoming reserved selected snapshot owned ticket current retained ambient
    simp [excluded] at descendant

theorem ownershipAmbient_cancel_supported_inactive (state : ConstructionState)
    (frame : OwnershipAmbientFrame) (outer : OwnershipAmbient)
    (valid : OwnershipAmbientInvariant state (frame :: outer))
    (token : ExitReservationId) (incoming reserved selected : DestinationId)
    (snapshot destination : PendingDestination)
    (owned : token ∈ frame.tickets)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (current : destinationCurrent state reserved = .ok selected)
    (present : state.destinations[selected]? = some destination)
    (inactive : activeProgress destination.progress = false)
    (supported : ReplacementSupported state selected) :
    cancelExitReservation token (completedCarrierIds frame.carriers) state = .ok () state :=
  cancelExitReservation_carried_branch state _ token incoming reserved selected snapshot ticket current
    (ownershipAmbient_selected_frontier state frame outer valid token incoming reserved selected snapshot destination
      owned ticket current present inactive supported)

theorem ownershipAmbient_unprotected_no_support (state : ConstructionState)
    (frame : OwnershipAmbientFrame) (outer : OwnershipAmbient)
    (valid : OwnershipAmbientInvariant state (frame :: outer))
    (token : ExitReservationId) (incoming reserved selected : DestinationId)
    (snapshot destination : PendingDestination)
    (owned : token ∈ frame.tickets)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (current : destinationCurrent state reserved = .ok selected)
    (present : state.destinations[selected]? = some destination)
    (inactive : activeProgress destination.progress = false)
    (unprotected : ¬ CarriedReservationBranch state selected (completedCarrierIds frame.carriers)) :
    ¬ ReplacementSupported state selected := by
  intro supported
  exact unprotected (ownershipAmbient_selected_frontier state frame outer valid token incoming reserved selected
    snapshot destination owned ticket current present inactive supported)

theorem liveFreshReservationRoles_direct_source (state : ConstructionState)
    (roles : LiveFreshReservationRoles state) (token : ExitReservationId)
    (incoming reserved current : DestinationId) (snapshot selected : PendingDestination)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (resolved : destinationCurrent state reserved = .ok current)
    (present : state.destinations[current]? = some selected)
    (direct : reserved = snapshot.capability.id) (inactive : activeProgress selected.progress = false) :
    ResumptionBackingSource state current snapshot := by
  have role := roles token incoming reserved current snapshot selected ticket resolved present
  rw [if_pos direct] at role
  exact ⟨selected, present, inactive, role.2⟩

theorem destinationCurrent_congr_tables (before after : ConstructionState)
    (rows : after.destinations = before.destinations)
    (successors : after.destinationSuccessors = before.destinationSuccessors) (incoming : DestinationId) :
    destinationCurrent after incoming = destinationCurrent before incoming := by
  have steps : ∀ fuel incoming, destinationCurrentSteps fuel after incoming = destinationCurrentSteps fuel before incoming := by
    intro fuel
    induction fuel with
    | zero => intro incoming; rfl
    | succ fuel previous =>
        intro incoming
        rw [destinationCurrentSteps_succ, destinationCurrentSteps_succ]
        simp only [rows, successors]
        split
        · cases found : before.destinationSuccessors.lookup incoming with
          | none => rfl
          | some next =>
              simp only [found]
              split
              · exact previous next
              · rfl
        · rfl
  unfold destinationCurrent
  simpa only [rows] using steps (before.destinations.size + 1) incoming

theorem liveFreshReservationRoles_metadata (before after : ConstructionState)
    (rows : after.destinations = before.destinations)
    (successors : after.destinationSuccessors = before.destinationSuccessors)
    (tickets : ∀ (token : ExitReservationId) (incoming reserved : DestinationId) (snapshot : PendingDestination),
      after.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
      before.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (roles : LiveFreshReservationRoles before) : LiveFreshReservationRoles after := by
  intro token incoming reserved current snapshot selected ticket resolved present
  apply roles token incoming reserved current snapshot selected (tickets token incoming reserved snapshot ticket)
  · simpa only [destinationCurrent_congr_tables before after rows successors] using resolved
  · simpa only [rows] using present

theorem liveFreshReservationRoles_restored (state : ConstructionState) (token : ExitReservationId)
    (resumptions : List (DestinationId × PendingDestination)) (roles : LiveFreshReservationRoles state) :
    LiveFreshReservationRoles { state with
      exitReservations := state.exitReservations.set! token .restored
      destinationResumptions := resumptions } := by
  apply liveFreshReservationRoles_metadata state
    { state with
      exitReservations := state.exitReservations.set! token .restored
      destinationResumptions := resumptions } rfl rfl _ roles
  intro index incoming reserved snapshot found
  by_cases same : token = index
  · subst index
    have inside : token < state.exitReservations.size := by
      simpa only [Array.size_set!] using (Array.getElem?_eq_some_iff.mp found).1
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt inside] at found
    simp at found
  · simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same] using found

theorem direct_resumption_insertion_sources (state : ConstructionState)
    (frame : OwnershipAmbientFrame) (outer : OwnershipAmbient)
    (valid : OwnershipAmbientInvariant state (frame :: outer))
    (token : ExitReservationId) (incoming reserved selected : DestinationId)
    (snapshot destination : PendingDestination) (owned : token ∈ frame.tickets)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (current : destinationCurrent state reserved = .ok selected)
    (present : state.destinations[selected]? = some destination)
    (direct : reserved = snapshot.capability.id) (inactive : activeProgress destination.progress = false)
    (unprotected : ¬ CarriedReservationBranch state selected (completedCarrierIds frame.carriers)) :
    let after := { state with
      exitReservations := state.exitReservations.set! token .restored
      destinationResumptions := (selected, snapshot) :: state.destinationResumptions }
    ResumptionBackingSources after ∧ UnsupportedResumptionKeys after ∧ LiveFreshReservationRoles after := by
  have source := liveFreshReservationRoles_direct_source state valid.structural.2.2.2.2.2
    token incoming reserved selected snapshot destination ticket current present direct inactive
  have unsupported := ownershipAmbient_unprotected_no_support state frame outer valid token incoming reserved selected
    snapshot destination owned ticket current present inactive unprotected
  refine ⟨?_, ?_, liveFreshReservationRoles_restored state token _ valid.structural.2.2.2.2.2⟩
  · intro id saved found
    by_cases same : selected = id
    · subst id
      have equal : snapshot = saved := by simpa [List.lookup] using found
      subst saved
      exact source
    · have old : state.destinationResumptions.lookup id = some saved := by
        simpa [List.lookup, beq_eq_false_iff_ne.mpr (Ne.symm same)] using found
      exact valid.structural.2.2.2.1 id saved old
  · intro id saved found supported
    have oldSupport := replacementSupported_congr_destinations
      { state with
        exitReservations := state.exitReservations.set! token .restored
        destinationResumptions := (selected, snapshot) :: state.destinationResumptions }
      state rfl id supported
    by_cases same : selected = id
    · subst id
      exact unsupported oldSupport
    · have old : state.destinationResumptions.lookup id = some saved := by
        simpa [List.lookup, beq_eq_false_iff_ne.mpr (Ne.symm same)] using found
      exact valid.structural.2.2.2.2.1 id saved old oldSupport

theorem retainedOutsideTickets_of_allocation_prefix (state : ConstructionState)
    (tokens : List ExitReservationId) (carriers : List Construct.Carrier) (first : Nat)
    (ordered : DestinationOwnersOrdered state)
    (allocated : ∀ id ∈ completedCarrierIds carriers, id < first)
    (fresh : ∀ (token : ExitReservationId) (incoming reserved selected : DestinationId)
      (snapshot : PendingDestination), token ∈ tokens →
      state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
      destinationCurrent state reserved = .ok selected → first ≤ selected) :
    RetainedOutsideTickets state tokens carriers := by
  intro token incoming reserved selected snapshot owned ticket current retained member
  exact destinationDescendant_false_of_lt state ordered selected retained
    (Nat.lt_of_lt_of_le (allocated retained member) (fresh token incoming reserved selected snapshot owned ticket current))

theorem liveFreshReservationRoles_waiting (state : ConstructionState) (token : ExitReservationId)
    (incoming : DestinationId) (roles : LiveFreshReservationRoles state) :
    LiveFreshReservationRoles { state with exitReservations := state.exitReservations.set! token (.waiting incoming) } := by
  apply liveFreshReservationRoles_metadata state
    { state with exitReservations := state.exitReservations.set! token (.waiting incoming) } rfl rfl _ roles
  intro index original reserved snapshot found
  by_cases same : token = index
  · subst index
    have inside : token < state.exitReservations.size := by
      simpa only [Array.size_set!] using (Array.getElem?_eq_some_iff.mp found).1
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt inside] at found
    simp at found
  · simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same] using found

theorem rearmExitReservation_finalState (receipt : BorrowedWaitingExitReservation) (state : ConstructionState) :
    (rearmExitReservation receipt state).finalState = state ∨
      (rearmExitReservation receipt state).finalState =
        { state with exitReservations := state.exitReservations.set! receipt.token (.waiting receipt.incoming) } := by
  unfold rearmExitReservation
  simp only [ConstructionM.get, bind]
  cases found : state.exitReservations[receipt.token]? with
  | none => exact Or.inl rfl
  | some reservation =>
      cases reservation with
      | waiting incoming | active role incoming reserved snapshot | released => exact Or.inl rfl
      | restored =>
          cases current : destinationCurrent state receipt.incoming with
          | error kind => exact Or.inl rfl
          | ok selected =>
              simp only [pure, bind, ConstructionM.set, lookupDestination_result]
              cases present : state.destinations[selected]? with
              | none => exact Or.inl rfl
              | some destination => exact Or.inr rfl

theorem liveFreshReservationRoles_rearm (receipt : BorrowedWaitingExitReservation) (state : ConstructionState)
    (roles : LiveFreshReservationRoles state) :
    LiveFreshReservationRoles (rearmExitReservation receipt state).finalState := by
  obtain unchanged | waiting := rearmExitReservation_finalState receipt state
  · simpa only [unchanged] using roles
  · simpa only [waiting] using liveFreshReservationRoles_waiting state receipt.token receipt.incoming roles

theorem rearmExitReservation_active_source (receipt : BorrowedWaitingExitReservation) (state : ConstructionState)
    (token : ExitReservationId) (role : ExitReservationRole) (incoming reserved : DestinationId)
    (snapshot : PendingDestination)
    (found : (rearmExitReservation receipt state).finalState.exitReservations[token]? =
      some (.active role incoming reserved snapshot)) :
    state.exitReservations[token]? = some (.active role incoming reserved snapshot) := by
  obtain unchanged | waiting := rearmExitReservation_finalState receipt state
  · simpa only [unchanged] using found
  · rw [waiting] at found
    by_cases same : receipt.token = token
    · rw [same] at found
      have inside : token < state.exitReservations.size := by
        simpa only [Array.size_set!] using (Array.getElem?_eq_some_iff.mp found).1
      simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt inside] at found
      simp at found
    · simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same] using found

theorem retainedReplacementAnchors_rearm (receipt : BorrowedWaitingExitReservation) (state : ConstructionState)
    (carriers : List Construct.Carrier) (anchors : RetainedReplacementAnchors state carriers) :
    RetainedReplacementAnchors (rearmExitReservation receipt state).finalState carriers := by
  obtain unchanged | waiting := rearmExitReservation_finalState receipt state
  · simpa only [unchanged] using anchors
  · rw [waiting]
    intro id row present inactive supported
    have original := replacementSupported_congr_destinations
      { state with exitReservations := state.exitReservations.set! receipt.token (.waiting receipt.incoming) }
      state rfl id supported
    exact anchors id row present inactive original

theorem retainedOutsideTickets_rearm (receipt : BorrowedWaitingExitReservation) (state : ConstructionState)
    (tokens : List ExitReservationId) (carriers : List Construct.Carrier)
    (outside : RetainedOutsideTickets state tokens carriers) :
    RetainedOutsideTickets (rearmExitReservation receipt state).finalState tokens carriers := by
  intro token incoming reserved selected snapshot member found resolved retained carried
  have original := rearmExitReservation_active_source receipt state token .fresh incoming reserved snapshot found
  obtain unchanged | waiting := rearmExitReservation_finalState receipt state
  · simpa only [unchanged] using outside token incoming reserved selected snapshot member original
      (by simpa only [unchanged] using resolved) retained carried
  · rw [waiting] at resolved ⊢
    have current : destinationCurrent state reserved = .ok selected := by
      simpa only [destinationCurrent_congr_tables state
        { state with exitReservations := state.exitReservations.set! receipt.token (.waiting receipt.incoming) } rfl rfl] using resolved
    exact outside token incoming reserved selected snapshot member original current retained carried

theorem ownershipAmbientBoundaries_rearm (receipt : BorrowedWaitingExitReservation) (state : ConstructionState)
    (ambient : OwnershipAmbient) (boundaries : OwnershipAmbientBoundaries state ambient) :
    OwnershipAmbientBoundaries (rearmExitReservation receipt state).finalState ambient := by
  induction ambient with
  | nil => trivial
  | cons frame outer previous =>
      exact ⟨retainedOutsideTickets_rearm receipt state frame.tickets (OwnershipAmbient.retained outer) boundaries.1,
        previous boundaries.2⟩

#print axioms ownershipAmbientBoundaries_rearm
#print axioms retainedReplacementAnchors_rearm
#print axioms rearmExitReservation_active_source
#print axioms rearmExitReservation_finalState
#print axioms liveFreshReservationRoles_rearm
#print axioms ownershipAmbient_selected_frontier
#print axioms ownershipAmbient_cancel_supported_inactive
#print axioms retainedOutsideTickets_of_allocation_prefix
#print axioms ownershipAmbientInvariant_capture_returned
#print axioms liveFreshReservationRoles_direct_source
#print axioms direct_resumption_insertion_sources

end Goose.Proofs.ConstructionExecutionOwnership
