import Goose.Proofs.ConstructionExitReservationRoles

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem accepted_open_reservation_resumption_roles (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved) :
    ResumptionReservationRoles reserved := by
  obtain ⟨allocated, replacement, appended, source, _, _⟩ :=
    accepted_open_reservation_allocation config initialized before reserved incoming selected token count receiver.destination
      receiver.present receiver.opened current ambient types live regions pending [] [] world reservation
  have fresh := reserve_open_replacement_fresh before.construction reserved incoming selected token count receiver.destination receiver.storage
    receiver.present receiver.opened receiver.bytes current reservation
  have map := openExitReplacement_successorMap incoming before.construction
  rw [replacement] at map
  simp only [ConstructionResult.finalState] at map
  have metadata := openExitReplacement_reservation_frame incoming before.construction world.ownership.source.structural.1.1.1
  rw [replacement] at metadata
  have resumptionMap : allocated.destinationResumptions = before.construction.destinationResumptions := by
    simpa only [ConstructionResult.finalState] using metadata.resumptions
  have noEdge : allocated.destinationSuccessors.lookup selected = none := by
    cases edge : allocated.destinationSuccessors.lookup selected with
    | none => rfl
    | some next =>
      have oldEdge : before.construction.destinationSuccessors.lookup selected = some next := by simpa only [map] using edge
      obtain ⟨earlier, later⟩ := world.ownership.source.structural.2.1 selected next oldEdge
      rw [fresh] at earlier
      exact False.elim (Nat.lt_irrefl _ (Nat.lt_trans earlier later))
  have oldKeyBound (id : Nat) (saved : PendingDestination)
      (found : before.construction.destinationResumptions.lookup id = some saved) : id < before.construction.destinations.size := by
    obtain ⟨front, suffix, equation, _⟩ := List.lookup_eq_some_iff.mp found
    have member : (id, saved) ∈ before.construction.destinationResumptions := by rw [equation]; simp
    exact (world.ownership.source.structural.1.1.2.resumptions (id, saved) member).allocated
  rw [appended]
  intro key saved found ticketId oldIncoming oldSelected snapshot ticket resolved
  by_cases new : ticketId = allocated.exitReservations.size
  · subst ticketId
    simp only [Array.getElem?_push, ↓reduceIte] at ticket
    cases ticket
    have path := destinationCurrent_successorPath { allocated with exitReservations := allocated.exitReservations.push (.active .fresh incoming selected receiver.destination) } selected key resolved
    have same : key = selected := by
      cases path with
      | refl => rfl
      | next edge remaining => simp only at edge; rw [noEdge] at edge; cases edge
    subst key
    have oldFound : before.construction.destinationResumptions.lookup selected = some saved := by
      simpa only [resumptionMap] using found
    have bound := oldKeyBound selected saved oldFound
    rw [fresh] at bound
    exact False.elim (Nat.lt_irrefl _ bound)
  · have oldTicket : allocated.exitReservations[ticketId]? = some (.active .fresh oldIncoming oldSelected snapshot) := by
      simpa [Array.getElem?_push, new] using ticket
    have oldResolved : destinationCurrent allocated oldSelected = .ok key := by
      simpa only [destinationCurrent_congr_tables allocated
        { allocated with exitReservations := allocated.exitReservations.push (.active .fresh incoming selected receiver.destination) }
        rfl rfl oldSelected] using resolved
    exact source.resumptionRoles key saved found ticketId oldIncoming oldSelected snapshot oldTicket oldResolved

#print axioms accepted_open_reservation_resumption_roles

theorem accepted_open_reservation_source_roles (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved) :
    LiveFreshReservationSuccessorRoles reserved ∧ DestinationSuccessorKeysInactive reserved ∧
    ResumptionReservationRoles reserved := by
  obtain ⟨allocated, replacement, appended, source, _, _⟩ :=
    accepted_open_reservation_allocation config initialized before reserved incoming selected token count receiver.destination
      receiver.present receiver.opened current ambient types live regions pending [] [] world reservation
  have inactive : DestinationSuccessorKeysInactive reserved := by
    rw [appended]
    exact source.inactiveKeys
  exact ⟨accepted_open_reservation_successor_roles config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending world reservation, inactive,
    accepted_open_reservation_resumption_roles config initialized before reserved incoming selected token count
      receiver current ambient types live regions pending world reservation⟩

#print axioms accepted_open_reservation_source_roles

end Goose.Proofs.ConstructionAcceptedExecution
