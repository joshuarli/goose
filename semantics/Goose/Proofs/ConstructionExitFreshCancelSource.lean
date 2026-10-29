import Goose.Proofs.ConstructionExitFreshCancelLifecycle

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem allocated_receiver_cancel_source_roles (config : EvalConfig) (initialized : Nat) (owner : ActId)
    (ty element : Goose.Construct.Ty) (request : ConstructionRequest) (origin : OriginId) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id : Nat) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (elementType : Goose.Construct.elementType ty = some element)
    (created : newDestination config.layout owner ty request origin none knownCount before = .ok id allocated) :
    ∃ reserved final,
      reserveExitDestination id .newValue allocated.construction = .ok (allocated.construction.exitReservations.size, id) reserved ∧
      (do
        cancelExitReservation allocated.construction.exitReservations.size []
        releaseExitReservation allocated.construction.exitReservations.size) reserved = .ok () final ∧
      ReservationLifecycleInvariant final ∧ DestinationSuccessorsValid final ∧ DestinationSuccessorKeysInactive final ∧
      LiveFreshReservationSuccessorRoles final ∧ LiveFreshReservationRawRoles final ∧ LiveFreshReservationRoles final ∧
      ResumptionReservationRoles final ∧
      RootedBackingObservations config.layout { allocated with construction := final } live (storageExtent before) ∧
      (∀ region ∈ regions, ReceivingProtection config.layout { allocated with construction := final } live region) ∧
      ∀ frame ∈ pending, CarriersLandingReady { allocated with construction := final } frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout { allocated with construction := final } carrier := by
  obtain ⟨reserved, final, reserve, cancel, lifecycle, rooted, regionsSafe, frames⟩ :=
    allocated_receiver_cancel_lifecycle config initialized owner ty element request origin knownCount before allocated id ambient types live
      regions pending world elementType created
  obtain ⟨otherReserved, otherFinal, otherReserve, otherCancel, savedSnapshot, ⟨frame⟩, savedEntries⟩ :=
    allocated_receiver_cancel_exact_frame config initialized owner ty element request origin knownCount before allocated id ambient types live
      regions pending world elementType created
  have sameReserved : otherReserved = reserved := (ConstructionResult.ok.inj (otherReserve.symm.trans reserve)).2
  subst otherReserved
  have sameFinal : otherFinal = final := (ConstructionResult.ok.inj (otherCancel.symm.trans cancel)).2
  subst otherFinal
  have successors : DestinationSuccessorsValid final := by
    intro key next edge
    have maps : final.destinationSuccessors = before.construction.destinationSuccessors := frame.successors
    have originalEdge : before.construction.destinationSuccessors.lookup key = some next := by
      simpa only [maps] using edge
    obtain ⟨ordered, bounded⟩ := world.ownership.source.structural.2.1 key next originalEdge
    exact ⟨ordered, Nat.lt_of_lt_of_le bounded frame.size⟩
  have inactive : DestinationSuccessorKeysInactive final := by
    intro key next edge
    have maps : final.destinationSuccessors = before.construction.destinationSuccessors := frame.successors
    have originalEdge : before.construction.destinationSuccessors.lookup key = some next := by
      simpa only [maps] using edge
    obtain ⟨row, present, inactive⟩ := world.ownership.source.inactiveKeys key next originalEdge
    have inside := (Array.getElem?_eq_some_iff.mp present).1
    exact ⟨row, (frame.lookup key inside).trans present, inactive⟩
  have aliases : LiveFreshReservationSuccessorRoles final := by
    intro token incoming selected node snapshot destination ticket path present
    have tickets : final.exitReservations = before.construction.exitReservations.push .released := frame.tickets
    have oldTicket : before.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot) := by
      simp only [tickets, Array.getElem?_push] at ticket
      split at ticket
      · cases ticket
      · exact ticket
    have maps : final.destinationSuccessors = before.construction.destinationSuccessors := frame.successors
    have oldPath : DestinationSuccessorPath before.construction selected node :=
      DestinationSuccessorPath.congr maps.symm path
    have selectedBound := (world.ownership.source.structural.1.1.2.active token .fresh incoming selected snapshot oldTicket).2.1
    have nodeBound := oldPath.bound world.ownership.source.structural.2.1 selectedBound
    have oldPresent : before.construction.destinations[node]? = some destination :=
      (frame.lookup node nodeBound).symm.trans present
    exact world.ownership.source.aliases token incoming selected node snapshot destination oldTicket oldPath oldPresent
  have resumptions : ResumptionReservationRoles final := by
    intro key saved savedFound token incoming selected snapshot ticket resolved
    have tickets : final.exitReservations = before.construction.exitReservations.push .released := frame.tickets
    have oldTicket : before.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot) := by
      simp only [tickets, Array.getElem?_push] at ticket
      split at ticket
      · cases ticket
      · exact ticket
    have selectedBound := (world.ownership.source.structural.1.1.2.active token .fresh incoming selected snapshot oldTicket).2.1
    obtain ⟨oldCurrent, oldResolved, _, oldBound, _⟩ := destinationCurrent_total before.construction
      world.ownership.source.structural.2.1 selected selectedBound
    have maps : final.destinationSuccessors = before.construction.destinationSuccessors := frame.successors
    have finalResolved := destinationCurrent_extension before.construction final maps frame.size selected oldCurrent oldResolved
    have keyEqual : key = oldCurrent := Except.ok.inj (resolved.symm.trans finalResolved)
    have fresh := newDestination_fresh_id config.layout owner ty request origin knownCount before allocated id created
    have different : key ≠ id := by
      rw [keyEqual, fresh]
      exact Nat.ne_of_lt oldBound
    have mismatch : (key == id) = false := beq_eq_false_iff_ne.mpr different
    have oldSaved : allocated.construction.destinationResumptions.lookup key = some saved := by
      simpa [savedEntries, List.lookup, mismatch] using savedFound
    obtain ⟨allocation⟩ := newDestination_fresh_frame config.layout owner ty request origin knownCount before allocated id
      world.ownership.source.structural.1.1.1 created
    have allocatedTicket : allocated.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot) := by
      rw [allocation.tickets]
      exact oldTicket
    have allocatedResolved := destinationCurrent_extension before.construction allocated.construction allocation.successors
      allocation.size selected oldCurrent oldResolved
    have allocatedWorld := newDestination_acceptedWorld config owner ty request origin knownCount initialized before allocated id
      ambient types live regions pending world created
    apply allocatedWorld.ownership.source.resumptionRoles key saved oldSaved token incoming selected snapshot allocatedTicket
    simpa only [keyEqual] using allocatedResolved
  exact ⟨reserved, final, reserve, cancel, lifecycle, successors, inactive, aliases,
    liveFreshReservationSuccessorRoles_raw final aliases, liveFreshReservationSuccessorRoles_current final aliases, resumptions,
    rooted, regionsSafe, frames⟩

#print axioms allocated_receiver_cancel_source_roles

end Goose.Proofs.ConstructionAcceptedExecution
