import Goose.Proofs.ConstructionExitFreshCancelProtected
import Goose.Proofs.ConstructionExecutionProtocolReservationCancel

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem allocated_receiver_cancel_lifecycle (config : EvalConfig) (initialized : Nat) (owner : ActId)
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
      ReservationLifecycleInvariant final ∧
      RootedBackingObservations config.layout { allocated with construction := final } live (storageExtent before) ∧
      (∀ region ∈ regions, ReceivingProtection config.layout { allocated with construction := final } live region) ∧
      ∀ frame ∈ pending, CarriersLandingReady { allocated with construction := final } frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout { allocated with construction := final } carrier := by
  obtain ⟨reserved, final, reserve, cancel, rooted, protectedRegions, frames⟩ :=
    allocated_receiver_cancel_protected config initialized owner ty element request origin knownCount before allocated id ambient types live
      regions pending world elementType created
  have allocatedWorld := newDestination_acceptedWorld config owner ty request origin knownCount initialized before allocated id
    ambient types live regions pending world created
  have reservedLife := reserveExitDestination_reservation_lifecycle id .newValue allocated.construction allocatedWorld.ownership.source.structural.1.1
  rw [reserve] at reservedLife
  simp only [ConstructionResult.finalState] at reservedLife
  have cancelLife := cancelExitReservation_lifecycle allocated.construction.exitReservations.size [] reserved reservedLife
  cases step : cancelExitReservation allocated.construction.exitReservations.size [] reserved with
  | fault reason stopped => simp [bind, step] at cancel
  | ok value middle =>
    cases value
    simp only [step, ConstructionResult.finalState] at cancelLife
    have releaseLife := releaseExitReservation_lifecycle middle allocated.construction.exitReservations.size cancelLife
    have release : releaseExitReservation allocated.construction.exitReservations.size middle = .ok () final := by
      simpa only [bind, step] using cancel
    rw [release] at releaseLife
    simp only [ConstructionResult.finalState] at releaseLife
    exact ⟨reserved, final, reserve, cancel, releaseLife, rooted, protectedRegions, frames⟩

#print axioms allocated_receiver_cancel_lifecycle

end Goose.Proofs.ConstructionAcceptedExecution
