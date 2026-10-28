import Goose.Proofs.ConstructionExitReservationAllocation
import Goose.Proofs.ConstructionExitByteReservationStorage
import Goose.Proofs.ConstructionExitReservationHistory

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem accepted_open_reservation_successor_roles (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved) :
    LiveFreshReservationSuccessorRoles reserved := by
  obtain ⟨allocated, replacement, appended, source, _, _⟩ :=
    accepted_open_reservation_allocation config initialized before reserved incoming selected token count receiver.destination
      receiver.present receiver.opened current ambient types live regions pending [] [] world reservation
  have fresh := reserve_open_replacement_fresh before.construction reserved incoming selected token count receiver.destination receiver.storage
    receiver.present receiver.opened receiver.bytes current reservation
  have indexed : receiver.destination.capability.id = incoming :=
    world.ownership.source.structural.1.1.1.2.1 incoming receiver.destination receiver.present
  have foundParent := open_replacement_parent_exact before.construction allocated incoming selected (count + 1)
    receiver.destination receiver.present receiver.opened replacement
  have links := openExitReplacement_success_parentLink before.construction allocated incoming selected replacement
  obtain ⟨parent, n, parentFound, parentPhase, link⟩ := links
  have sameParent := Option.some.inj (parentFound.symm.trans foundParent)
  subst parent
  simp only [DestinationForwardLink] at link
  obtain ⟨replacementRow, replacementFound, replacementUse, replacementBacking⟩ := link
  have map := openExitReplacement_successorMap incoming before.construction
  rw [replacement] at map
  simp only [ConstructionResult.finalState] at map
  have noEdge : allocated.destinationSuccessors.lookup selected = none := by
    cases edge : allocated.destinationSuccessors.lookup selected with
    | none => rfl
    | some next =>
      have oldEdge : before.construction.destinationSuccessors.lookup selected = some next := by simpa only [map] using edge
      have bound := world.ownership.source.structural.2.1 selected next oldEdge
      have earlier := bound.1
      have later := bound.2
      rw [fresh] at earlier
      exact False.elim (Nat.lt_irrefl _ (Nat.lt_trans earlier later))
  have distinct : selected ≠ receiver.destination.capability.id := by
    rw [indexed, fresh]
    exact Nat.ne_of_gt (Array.getElem?_eq_some_iff.mp receiver.present).1
  have distinctIncoming : selected ≠ incoming := by simpa only [indexed] using distinct
  rw [appended]
  intro ticketId oldIncoming oldSelected node saved chosen ticket path chosenFound
  by_cases new : ticketId = allocated.exitReservations.size
  · subst ticketId
    simp only [Array.getElem?_push, Nat.lt_irrefl, ↓reduceIte] at ticket
    cases ticket
    have sameNode : node = selected := by
      cases path with
      | refl => rfl
      | next edge remaining => simp only at edge; rw [noEdge] at edge; cases edge
    subst node
    have sameChosen := Option.some.inj (chosenFound.symm.trans replacementFound)
    subst chosen
    simp [distinctIncoming, indexed, replacementUse, replacementBacking]
  · have oldTicket : allocated.exitReservations[ticketId]? = some (.active .fresh oldIncoming oldSelected saved) := by
      simpa [Array.getElem?_push, new] using ticket
    exact source.aliases ticketId oldIncoming oldSelected node saved chosen oldTicket
      (DestinationSuccessorPath.congr (before := { allocated with exitReservations := allocated.exitReservations.push (.active .fresh incoming selected receiver.destination) }) (after := allocated) rfl path) chosenFound

#print axioms accepted_open_reservation_successor_roles

theorem accepted_open_reservation_context_parts (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (channels : List Channel) (carriers : List Goose.Construct.Carrier)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (history : ReservationReferencesBounded before.construction ambient)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved) :
    LiveFreshReservationSuccessorRoles reserved ∧
    ReservationReferencesBounded reserved (.exitChannels [token] channels carriers :: ambient) ∧
    OwnershipReservationFrames reserved (.exitChannels [token] channels carriers :: ambient) ∧
    OwnershipRuntimeFrames { before with construction := reserved } (.exitChannels [token] channels carriers :: ambient) ∧
    OwnershipRuntimeIdentities { before with construction := reserved } ∧
    OwnershipCapturedReceivingBounds reserved (.exitChannels [token] channels carriers :: ambient) ∧
    OwnershipCapturedReceivingFrames reserved (.exitChannels [token] channels carriers :: ambient) := by
  have roles := accepted_open_reservation_successor_roles config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending world reservation
  have frames := accepted_fresh_reservation_frames config initialized before reserved incoming token selected
    ambient types live regions pending world reservation channels carriers
  have captured := accepted_reservation_captured_from_history config initialized before reserved incoming selected token count
    receiver.destination receiver.present receiver.opened current ambient types live regions pending channels carriers world history reservation
  exact ⟨roles, captured.1, frames.2.2.1, frames.2.2.2.1, frames.2.2.2.2, captured.2.1, captured.2.2⟩

#print axioms accepted_open_reservation_context_parts

end Goose.Proofs.ConstructionAcceptedExecution
