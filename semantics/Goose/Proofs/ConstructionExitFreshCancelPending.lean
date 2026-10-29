import Goose.Proofs.ConstructionExitFreshCancelRegions
import Goose.Proofs.ConstructionExitWaitingCarrier

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

private theorem cancelled_leaf_exact (state : ConstructionState)
    (token incoming reserved selected count : Nat) (snapshot row : PendingDestination) (storage : ReceivingStorage)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (current : destinationCurrent state reserved = .ok selected)
    (present : state.destinations[selected]? = some row) (identity : row.capability.id = selected)
    (phase : row.progress = .open count ∨ row.progress = .built count)
    (writable : destinationCanWrite state selected = true) (stored : state.storage[row.storage]? = some storage)
    (leaf : treeRows state selected = [row]) (direct : reserved = snapshot.capability.id) :
    let cleaned := abandonRowState state selected row storage
    let cancelled := { cleaned with
      destinationResumptions := (selected, snapshot) :: cleaned.destinationResumptions
      exitReservations := cleaned.exitReservations.set! token .restored }
    (do cancelExitReservation token []; releaseExitReservation token) state =
      .ok () { cancelled with exitReservations := cancelled.exitReservations.set! token .released } := by
  let cleaned := abandonRowState state selected row storage
  let cancelled := { cleaned with
    destinationResumptions := (selected, snapshot) :: cleaned.destinationResumptions
    exitReservations := cleaned.exitReservations.set! token .restored }
  have tree := abandon_leaf_success state selected count row storage present identity phase writable stored leaf
  have active : activeRow row = true := by rcases phase with phase | phase <;> simp [activeRow, phase]
  have cancelledResult := cancel_active_direct_saves_snapshot state cleaned token incoming reserved selected snapshot row
    ticket current present active tree direct
  have inside : token < cleaned.exitReservations.size := (Array.getElem?_eq_some_iff.mp ticket).1
  have restored : cancelled.exitReservations[token]? = some .restored := by
    simp only [cancelled, Array.set!_eq_setIfInBounds]
    exact Array.getElem?_setIfInBounds_self_of_lt inside
  simp only [bind, show cancelExitReservation token [] state = .ok () cancelled from cancelledResult]
  change releaseExitReservation token cancelled = _
  simp only [releaseExitReservation, ConstructionM.get, bind, restored, ConstructionM.set]
  rfl

theorem allocated_receiver_cancel_exact_frame (config : EvalConfig) (initialized : Nat) (owner : ActId)
    (ty element : Goose.Construct.Ty) (request : ConstructionRequest) (origin : OriginId) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id : Nat) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (elementType : Goose.Construct.elementType ty = some element)
    (created : newDestination config.layout owner ty request origin none knownCount before = .ok id allocated) :
    ∃ reserved final,
      reserveExitDestination id .newValue allocated.construction = .ok (allocated.construction.exitReservations.size, id) reserved ∧
      (do cancelExitReservation allocated.construction.exitReservations.size []
          releaseExitReservation allocated.construction.exitReservations.size) reserved = .ok () final ∧
      ∃ snapshot, Nonempty (FreshDestinationFrame { before with construction := { before.construction with
        exitReservations := before.construction.exitReservations.push .released } } { allocated with construction := final }) ∧
        final.destinationResumptions = (id, snapshot) :: allocated.construction.destinationResumptions ∧
        snapshot.progress = .open 0 ∧ snapshot.use = .receiver ∧
        final.destinations[id]? = some { snapshot with progress := .abandoned } ∧
        allocated.construction.destinations[id]? = some snapshot ∧
        final.destinations = allocated.construction.destinations.set! id { snapshot with progress := .abandoned } := by
  obtain ⟨⟨backing⟩, _⟩ := newDestination_open_ready config initialized owner ty request origin knownCount
    before allocated ambient types live regions pending id element world elementType created
  obtain ⟨newest, receiver, receiverFound, receiverUse⟩ := newDestination_newest_receiver config.layout owner ty request
    origin knownCount before allocated id created
  have same : receiver = backing.destination := Option.some.inj (receiverFound.symm.trans backing.present)
  subst receiver
  have current := newDestination_current_self config initialized owner ty request origin knownCount before allocated id
    ambient types live regions pending world created
  obtain ⟨allocation⟩ := newDestination_fresh_frame config.layout owner ty request origin knownCount before allocated id
    world.ownership.source.structural.1.1.1 created
  have fresh := newDestination_fresh_id config.layout owner ty request origin knownCount before allocated id created
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
  have identity := lifecycle.1.2.1 id backing.destination backing.present
  have direct : id = backing.destination.capability.id := identity.symm
  have reservedCurrent : destinationCurrent reserved id = .ok id :=
    (destinationCurrent_congr_tables allocated.construction reserved rfl rfl id).trans current
  have leaf := newest_active_destination_is_leaf reserved id backing.destination backing.present
    (by simp [activeRow, backing.opened]) newest lifecycle.1.2.1 lifecycle.1.2.2.2
  have writable := receiver_destination_writable reserved id backing.destination backing.present receiverUse
  let cleaned := abandonRowState reserved id backing.destination backing.storage
  let cancelled := { cleaned with
    destinationResumptions := (id, backing.destination) :: cleaned.destinationResumptions
    exitReservations := cleaned.exitReservations.set! allocated.construction.exitReservations.size .restored }
  let final := { cancelled with exitReservations := cancelled.exitReservations.set! allocated.construction.exitReservations.size .released }
  have cancel : (do
      cancelExitReservation allocated.construction.exitReservations.size []
      releaseExitReservation allocated.construction.exitReservations.size) reserved = .ok () final :=
    cancelled_leaf_exact reserved allocated.construction.exitReservations.size id id id 0 backing.destination backing.destination
      backing.storage ticket reservedCurrent backing.present identity (Or.inl backing.opened) writable backing.bytes leaf direct
  let beforeReleased := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push .released } }
  have allocationRow : allocation.row = backing.destination := by
    have found : allocated.construction.destinations[id]? = some allocation.row := by
      rw [allocation.destinations, fresh]
      exact Array.getElem?_push_size
    exact Option.some.inj (found.symm.trans backing.present)
  have fullFrame : FreshDestinationFrame beforeReleased { allocated with construction := final } := by
    refine ⟨?_, { backing.destination with progress := .abandoned }, ?_, ?_, ?_, ?_, ?_⟩
    · change { allocated with construction := final } = { beforeReleased with construction := final }
      rw [allocation.outer]
    · change final.destinations = before.construction.destinations.push { backing.destination with progress := .abandoned }
      simp only [final, cancelled, cleaned, abandonRowState, reserved]
      rw [allocation.destinations, allocationRow]
      simp [fresh, Array.set!_eq_setIfInBounds, Array.setIfInBounds, Array.set_push]
    · exact receiverUse
    · exact allocation.successors
    · change final.exitReservations = before.construction.exitReservations.push .released
      simp [final, cancelled, cleaned, abandonRowState, reserved, allocation.tickets,
        Array.set!_eq_setIfInBounds, Array.setIfInBounds, Array.set_push]
    · intro index storage present
      have original : before.construction.storage[index]? = some storage := present
      have old := allocation.storage index storage original
      have priorBound := (Array.getElem?_eq_some_iff.mp original).1
      obtain ⟨freshRow, freshFound, freshBacking, freshStorage⟩ := newDestination_success_fresh config.layout owner ty request
        origin knownCount before allocated id created
      have sameRow : freshRow = backing.destination := Option.some.inj (freshFound.symm.trans backing.present)
      subst freshRow
      have different : index ≠ backing.destination.storage := by omega
      change (reserved.storage.set! backing.destination.storage _)[index]? = some storage
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm different)]
      exact old
  have abandonedFound : final.destinations[id]? = some { backing.destination with progress := .abandoned } := by
    change (allocated.construction.destinations.set! id { backing.destination with progress := .abandoned })[id]? = _
    rw [Array.set!_eq_setIfInBounds]
    exact Array.getElem?_setIfInBounds_self_of_lt (Array.getElem?_eq_some_iff.mp backing.present).1
  exact ⟨reserved, final, reservation, cancel, backing.destination, ⟨fullFrame⟩, rfl, backing.opened, receiverUse, abandonedFound, backing.present, rfl⟩

theorem allocated_receiver_cancel_frame (config : EvalConfig) (initialized : Nat) (owner : ActId)
    (ty element : Goose.Construct.Ty) (request : ConstructionRequest) (origin : OriginId) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id : Nat) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (elementType : Goose.Construct.elementType ty = some element)
    (created : newDestination config.layout owner ty request origin none knownCount before = .ok id allocated) :
    ∃ reserved final,
      reserveExitDestination id .newValue allocated.construction = .ok (allocated.construction.exitReservations.size, id) reserved ∧
      (do cancelExitReservation allocated.construction.exitReservations.size []
          releaseExitReservation allocated.construction.exitReservations.size) reserved = .ok () final ∧
      Nonempty (FreshDestinationFrame { before with construction := { before.construction with
        exitReservations := before.construction.exitReservations.push .released } } { allocated with construction := final }) := by
  obtain ⟨reserved, final, reservation, cancel, snapshot, frame, saved, opened, use, found, prior, rows⟩ := allocated_receiver_cancel_exact_frame config initialized owner
    ty element request origin knownCount before allocated id ambient types live regions pending world elementType created
  exact ⟨reserved, final, reservation, cancel, frame⟩

theorem allocated_receiver_cancel_pending (config : EvalConfig) (initialized : Nat) (owner : ActId)
    (ty element : Goose.Construct.Ty) (request : ConstructionRequest) (origin : OriginId) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id : Nat) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (elementType : Goose.Construct.elementType ty = some element)
    (created : newDestination config.layout owner ty request origin none knownCount before = .ok id allocated) :
    ∃ reserved final,
      reserveExitDestination id .newValue allocated.construction = .ok (allocated.construction.exitReservations.size, id) reserved ∧
      (do cancelExitReservation allocated.construction.exitReservations.size []
          releaseExitReservation allocated.construction.exitReservations.size) reserved = .ok () final ∧
      ∀ pendingFrame ∈ pending,
        CarriersLandingReady { allocated with construction := final } pendingFrame.channels pendingFrame.carriers ∧
        ∀ carrier ∈ pendingFrame.carriers, CarrierResultBacking config.layout { allocated with construction := final } carrier := by
  obtain ⟨reserved, final, reservation, cancel, ⟨fullFrame⟩⟩ := allocated_receiver_cancel_frame config initialized owner ty element
    request origin knownCount before allocated id ambient types live regions pending world elementType created
  refine ⟨reserved, final, reservation, cancel, ?_⟩
  intro pendingFrame member
  have ready := appended_ticket_pending_carrier_ready config initialized before ambient types live regions pending .released world pendingFrame member
  have backing := appended_ticket_pending_carrier_backing config initialized before ambient types live regions pending .released world pendingFrame member
  exact ⟨fullFrame.carriers_ready pendingFrame.channels pendingFrame.carriers ready,
    fun carrier carried => fullFrame.carrier_backing config.layout carrier (backing carrier carried)⟩

#print axioms allocated_receiver_cancel_exact_frame
#print axioms allocated_receiver_cancel_frame

#print axioms allocated_receiver_cancel_pending

end Goose.Proofs.ConstructionAcceptedExecution
