import Goose.Proofs.ConstructionExitReservationStructural
import Goose.Proofs.ConstructionExitByteReservationPrefix

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem accepted_open_reservation_new_boundary (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (retained : ∀ id ∈ completedCarrierIds ambient.retained, id < before.construction.destinations.size) :
    RetainedOutsideTickets reserved [token] ambient.retained := by
  obtain ⟨allocated, replacement, appended, source, _, _⟩ :=
    accepted_open_reservation_allocation config initialized before reserved incoming selected token count receiver.destination
      receiver.present receiver.opened current ambient types live regions pending [] [] world reservation
  have fresh := reserve_open_replacement_fresh before.construction reserved incoming selected token count receiver.destination receiver.storage
    receiver.present receiver.opened receiver.bytes current reservation
  have selectedTicket := (reserve_open_receiver_snapshot before.construction reserved incoming selected token count receiver.destination
    receiver.present receiver.opened current reservation).2
  have map := openExitReplacement_successorMap incoming before.construction
  rw [replacement] at map
  simp only [ConstructionResult.finalState] at map
  have noEdge : reserved.destinationSuccessors.lookup selected = none := by
    rw [appended]
    cases edge : allocated.destinationSuccessors.lookup selected with
    | none => rfl
    | some next =>
      have old : before.construction.destinationSuccessors.lookup selected = some next := by simpa only [map] using edge
      obtain ⟨earlier, later⟩ := world.ownership.source.structural.2.1 selected next old
      rw [fresh] at earlier
      exact False.elim (Nat.lt_irrefl _ (Nat.lt_trans earlier later))
  intro id oldIncoming oldSelected resolved saved member ticket currentResult kept keptMember
  simp only [List.mem_singleton] at member
  subst id
  have same := Option.some.inj (ticket.symm.trans selectedTicket)
  cases same
  have path := destinationCurrent_successorPath reserved selected resolved currentResult
  have sameResolved : resolved = selected := by
    cases path with
    | refl => rfl
    | next edge rest => rw [noEdge] at edge; cases edge
  subst resolved
  have ordered := (accepted_open_reservation_source config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending world reservation).structural.1.1.1.2.2.2
  apply destinationDescendant_false_of_lt reserved ordered selected kept
  rw [fresh]
  exact retained kept keptMember

theorem completed_carriers_bounded_by_pending (config : EvalConfig) (initialized : Nat)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (covered : ∀ id, .completed id ∈ ambient.retained → ∃ frame ∈ pending, .completed id ∈ frame.carriers) :
    ∀ id ∈ completedCarrierIds ambient.retained, id < state.construction.destinations.size := by
  intro id member
  simp only [completedCarrierIds, List.mem_filterMap] at member
  obtain ⟨carrier, present, found⟩ := member
  cases carrier with
  | register value => simp at found
  | pendingNamed token => simp at found
  | completed actual =>
    simp only [Option.some.injEq] at found
    subst actual
    obtain ⟨frame, frameMember, carrierMember⟩ := covered id present
    have backing := (world.carriers frame frameMember).2 (.completed id) carrierMember
    cases backing with
    | completed id count row stored rowPresent built sampled backed =>
      exact (Array.getElem?_eq_some_iff.mp rowPresent).1

theorem accepted_open_reservation_boundary_from_pending (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (covered : ∀ id, .completed id ∈ ambient.retained → ∃ frame ∈ pending, .completed id ∈ frame.carriers) :
    RetainedOutsideTickets reserved [token] ambient.retained :=
  accepted_open_reservation_new_boundary config initialized before reserved incoming selected token count receiver current
    ambient types live regions pending world reservation
    (completed_carriers_bounded_by_pending config initialized before ambient types live regions pending world covered)

theorem accepted_open_reservation_world_parts (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (channels : List Channel) (carriers : List Goose.Construct.Carrier)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (history : ReservationReferencesBounded before.construction ambient)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (covered : ∀ id, .completed id ∈ ambient.retained → ∃ frame ∈ pending, .completed id ∈ frame.carriers)
    (region : ReceivingRegion) (member : region ∈ regions) (destination : region.destination = incoming) :
    OwnershipSourceState reserved ∧
    OwnershipReservationFrames reserved (.exitChannels [token] channels carriers :: ambient) ∧
    OwnershipRuntimeFrames { before with construction := reserved } (.exitChannels [token] channels carriers :: ambient) ∧
    OwnershipRuntimeIdentities { before with construction := reserved } ∧
    OwnershipCapturedReceivingBounds reserved (.exitChannels [token] channels carriers :: ambient) ∧
    OwnershipCapturedReceivingFrames reserved (.exitChannels [token] channels carriers :: ambient) ∧
    RetainedOutsideTickets reserved [token] ambient.retained ∧
    ReceivingProtection config.layout { before with construction := reserved } live
      { region with mutableDestinations := selected :: region.mutableDestinations } := by
  have parts := accepted_open_reservation_context_parts config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending channels carriers world history reservation
  exact ⟨accepted_open_reservation_source config initialized before reserved incoming selected token count
      receiver current ambient types live regions pending world reservation,
    parts.2.2.1, parts.2.2.2.1, parts.2.2.2.2.1, parts.2.2.2.2.2.1, parts.2.2.2.2.2.2,
    accepted_open_reservation_boundary_from_pending config initialized before reserved incoming selected token count
      receiver current ambient types live regions pending world reservation covered,
    reserve_open_extended_protection config.layout before reserved incoming selected token count receiver current reservation
      live region destination (world.protections region member)⟩

#print axioms accepted_open_reservation_new_boundary
#print axioms completed_carriers_bounded_by_pending
#print axioms accepted_open_reservation_boundary_from_pending
#print axioms accepted_open_reservation_world_parts

end Goose.Proofs.ConstructionAcceptedExecution
