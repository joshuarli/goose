import Goose.Proofs.ConstructionExitWaitingSource
import Goose.Proofs.ConstructionExitDirectSourceRoles

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem direct_fresh_ambient_separated (state : ConstructionState) (incoming : Nat) (row : PendingDestination)
    (ambient : OwnershipAmbient) (carriers : List Goose.Construct.Carrier) (source : OwnershipSourceState state)
    (valid : OwnershipAmbientInvariant state ambient)
    (history : ReservationReferencesBounded state ambient)
    (present : state.destinations[incoming]? = some row) (opened : row.progress = .open 0)
    (currentSelf : destinationCurrent state incoming = .ok incoming)
    (separated : ∀ retained ∈ completedCarrierIds ambient.retained,
      destinationDescendant state.destinations incoming retained = false) :
    OwnershipAmbientInvariant
      { state with exitReservations := state.exitReservations.push (.active .fresh incoming incoming row) }
      (.exitChannels [state.exitReservations.size] [] carriers :: ambient) := by
  let reserved := { state with exitReservations := state.exitReservations.push (.active .fresh incoming incoming row) }
  have sourceAfter := direct_fresh_source_state state incoming row source present opened currentSelf
  have unreferenced := reservationReferencesBounded_unreferenced state ambient history
  have oldTicket (token oldIncoming selected : Nat) (snapshot : PendingDestination)
      (different : token ≠ state.exitReservations.size)
      (ticket : reserved.exitReservations[token]? = some (.active .fresh oldIncoming selected snapshot)) :
      state.exitReservations[token]? = some (.active .fresh oldIncoming selected snapshot) := by
    simpa [reserved, Array.getElem?_push, different] using ticket
  have supportBefore : ∀ id, ReplacementSupported reserved id → ReplacementSupported state id := by
    intro id supported
    induction supported with
    | active id row found phase => exact .active id row found phase
    | parent id parent row found use supported ih => exact .parent id parent row found use ih
  have boundaries : ∀ frames : OwnershipAmbient, ReservationTokenUnreferenced state.exitReservations.size frames →
      OwnershipAmbientBoundaries state frames → OwnershipAmbientBoundaries reserved frames := by
    intro frames
    induction frames with
    | nil => intro _ _; trivial
    | cons frame rest ih =>
      intro fresh old
      have head := fresh frame (by simp)
      have tail : ReservationTokenUnreferenced state.exitReservations.size rest := by
        intro item member
        exact fresh item (List.mem_cons_of_mem frame member)
      refine ⟨?_, ih tail old.2⟩
      intro token oldIncoming selected current snapshot owned ticket resolved retained member
      have different : token ≠ state.exitReservations.size := by
        intro same
        subst token
        exact head.1 owned
      rw [destinationCurrent_congr_tables state reserved rfl rfl selected] at resolved
      exact old.1 token oldIncoming selected current snapshot owned
        (oldTicket token oldIncoming selected snapshot different ticket) resolved retained member
  change OwnershipAmbientInvariant reserved (.exitChannels [state.exitReservations.size] [] carriers :: ambient)
  refine ⟨sourceAfter.structural.1, ?_, ?_, boundaries ambient unreferenced valid.boundaries⟩
  · intro id destination found inactive supported
    obtain ⟨retained, member, ancestry⟩ := valid.anchors id destination found inactive (supportBefore id supported)
    refine ⟨retained, ?_, ancestry⟩
    simp only [OwnershipAmbient.retained, List.flatMap_cons, OwnershipAmbientFrame.carriers, completedCarrierIds, List.filterMap_append, List.mem_append]
    exact Or.inr member
  · intro token oldIncoming selected current snapshot owned ticket resolved retained member
    simp only [OwnershipAmbientFrame.tickets, List.mem_singleton] at owned
    subst token
    have same : (.active .fresh oldIncoming selected snapshot : ExitReservation) = .active .fresh incoming incoming row := by
      have found : reserved.exitReservations[state.exitReservations.size]? = some (.active .fresh incoming incoming row) := by simp [reserved]
      exact Option.some.inj (ticket.symm.trans found)
    cases same
    rw [destinationCurrent_congr_tables state reserved rfl rfl incoming] at resolved
    have sameCurrent : current = incoming := Except.ok.inj (resolved.symm.trans currentSelf)
    subst current
    exact separated retained member

theorem direct_fresh_ambient (state : ConstructionState) (incoming : Nat) (row : PendingDestination)
    (ambient : OwnershipAmbient) (carriers : List Goose.Construct.Carrier) (source : OwnershipSourceState state)
    (valid : OwnershipAmbientInvariant state ambient)
    (history : ReservationReferencesBounded state ambient)
    (present : state.destinations[incoming]? = some row) (opened : row.progress = .open 0)
    (current : destinationCurrent state incoming = .ok incoming)
    (noRetained : completedCarrierIds ambient.retained = []) :
    OwnershipAmbientInvariant
      { state with exitReservations := state.exitReservations.push (.active .fresh incoming incoming row) }
      (.exitChannels [state.exitReservations.size] [] carriers :: ambient) := by
  apply direct_fresh_ambient_separated state incoming row ambient carriers source valid history present opened current
  intro retained member
  rw [noRetained] at member
  cases member

#print axioms direct_fresh_ambient_separated
#print axioms direct_fresh_ambient
end Goose.Proofs.ConstructionAcceptedExecution
