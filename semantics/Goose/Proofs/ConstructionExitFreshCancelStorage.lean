import Goose.Proofs.ConstructionExitNewReceiverFrontier
import Goose.Proofs.ConstructionExitLeafStorage
import Goose.Proofs.ConstructionAcceptedOpenDestination
import Goose.Proofs.ConstructionAcceptedOwnerLineage

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem allocated_receiver_cancel_old_storage (config : EvalConfig) (initialized : Nat) (owner : ActId)
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
      (∀ (index : Nat) (storage : ReceivingStorage), before.construction.storage[index]? = some storage →
        final.storage[index]? = some storage) := by
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
  have leaf := newest_active_destination_is_leaf reserved id backing.destination backing.present
    (by simp [activeRow, backing.opened]) newest lifecycle.1.2.1 lifecycle.1.2.2.2
  have writable := Goose.Proofs.ExitExecution.receiver_destination_writable reserved id backing.destination backing.present receiverUse
  obtain ⟨final, cancelled, unchanged⟩ := cancel_leaf_preserves_other_storage reserved
    allocated.construction.exitReservations.size id id id 0 backing.destination backing.destination backing.storage
    ticket reservedCurrent backing.present (lifecycle.1.2.1 id backing.destination backing.present)
    (Or.inl backing.opened) writable backing.bytes leaf direct lifecycle
  obtain ⟨freshRow, freshFound, freshBacking, freshStorage⟩ := newDestination_success_fresh config.layout owner ty request
    origin knownCount before allocated id created
  have sameRow : freshRow = backing.destination := Option.some.inj (freshFound.symm.trans backing.present)
  subst freshRow
  obtain ⟨frame⟩ := newDestination_fresh_frame config.layout owner ty request origin knownCount before allocated id
    world.ownership.source.structural.1.1.1 created
  refine ⟨reserved, final, reservation, cancelled, ?_⟩
  intro index storage present
  have bound := (Array.getElem?_eq_some_iff.mp present).1
  have different : index ≠ backing.destination.storage := by omega
  have same := unchanged index different
  exact same.trans (frame.storage index storage present)

#print axioms allocated_receiver_cancel_old_storage

end Goose.Proofs.ConstructionAcceptedExecution
