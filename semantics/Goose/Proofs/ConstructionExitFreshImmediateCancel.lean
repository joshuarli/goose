import Goose.Proofs.ConstructionExitNewReceiverFrontier
import Goose.Proofs.ConstructionAcceptedOpenDestination
import Goose.Proofs.ConstructionAcceptedOwnerLineage

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem allocated_receiver_direct_cancel (config : EvalConfig) (initialized : Nat) (owner : ActId)
    (ty element : Goose.Construct.Ty) (request : ConstructionRequest) (origin : OriginId) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id : Nat) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (elementType : Goose.Construct.elementType ty = some element)
    (created : newDestination config.layout owner ty request origin none knownCount before = .ok id allocated) :
    ∃ reserved final,
      reserveExitDestination id .newValue allocated.construction =
        .ok (allocated.construction.exitReservations.size, id) reserved ∧
      (do
        cancelExitReservation allocated.construction.exitReservations.size []
        releaseExitReservation allocated.construction.exitReservations.size) reserved = .ok () final ∧
      (∀ index, index < id → final.destinations[index]? = allocated.construction.destinations[index]?) ∧
      (∀ other, other ≠ allocated.construction.exitReservations.size →
        final.exitReservations[other]? = allocated.construction.exitReservations[other]?) := by
  obtain ⟨⟨backing⟩, _⟩ := newDestination_open_ready config initialized owner ty request origin knownCount
    before allocated ambient types live regions pending id element world elementType created
  obtain ⟨newest, receiver, receiverFound, receiverUse⟩ := newDestination_newest_receiver config.layout owner ty request
    origin knownCount before allocated id created
  have same : receiver = backing.destination := Option.some.inj (receiverFound.symm.trans backing.present)
  subst receiver
  have current := newDestination_current_self config initialized owner ty request origin knownCount before allocated id
    ambient types live regions pending world created
  let reserved := { allocated.construction with
    exitReservations := allocated.construction.exitReservations.push (.active .fresh id id backing.destination) }
  have reservation : reserveExitDestination id .newValue allocated.construction =
      .ok (allocated.construction.exitReservations.size, id) reserved :=
    reserve_open_zero_direct allocated.construction id backing.destination backing.present backing.opened current
  have allocatedWorld := newDestination_acceptedWorld config owner ty request origin knownCount initialized before allocated id
    ambient types live regions pending world created
  have lifecycle := reserveExitDestination_reservation_lifecycle id .newValue allocated.construction allocatedWorld.ownership.source.structural.1.1
  rw [reservation] at lifecycle
  have ticket : reserved.exitReservations[allocated.construction.exitReservations.size]? =
      some (.active .fresh id id backing.destination) := by simp [reserved]
  have direct : id = backing.destination.capability.id := by
    exact (allocatedWorld.ownership.source.structural.1.1.1.2.1 id backing.destination backing.present).symm
  have reservedCurrent : destinationCurrent reserved id = .ok id :=
    (destinationCurrent_congr_tables allocated.construction reserved rfl rfl id).trans current
  obtain ⟨final, cancelled, rows, tickets⟩ := cancel_newest_direct_receiver_preserves_older reserved
    allocated.construction.exitReservations.size id id id 0 backing.destination backing.destination backing.storage
    ticket reservedCurrent backing.present receiverUse (Or.inl backing.opened) backing.bytes newest direct lifecycle
  refine ⟨reserved, final, reservation, cancelled, rows, ?_⟩
  intro other different
  simpa [reserved, Array.getElem?_push, different] using tickets other different

#print axioms allocated_receiver_direct_cancel

end Goose.Proofs.ConstructionAcceptedExecution
