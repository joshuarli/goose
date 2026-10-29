import Goose.Proofs.ConstructionExitFreshCancelPending

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem allocated_receiver_cancel_protected (config : EvalConfig) (initialized : Nat) (owner : ActId)
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
      RootedBackingObservations config.layout { allocated with construction := final } live (storageExtent before) ∧
      (∀ region ∈ regions, ReceivingProtection config.layout { allocated with construction := final } live region) ∧
      ∀ frame ∈ pending, CarriersLandingReady { allocated with construction := final } frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout { allocated with construction := final } carrier := by
  obtain ⟨reserved, final, reserve, cancel, rooted⟩ := allocated_receiver_cancel_rooted config initialized owner ty element request origin
    knownCount before allocated id ambient types live regions pending world elementType created
  obtain ⟨otherReserved, otherFinal, otherReserve, otherCancel, regionsSafe⟩ := allocated_receiver_cancel_regions config initialized owner
    ty element request origin knownCount before allocated id ambient types live regions pending world elementType created
  have sameReserved : otherReserved = reserved := (ConstructionResult.ok.inj (otherReserve.symm.trans reserve)).2
  subst otherReserved
  have sameFinal : otherFinal = final := (ConstructionResult.ok.inj (otherCancel.symm.trans cancel)).2
  subst otherFinal
  obtain ⟨otherReserved, otherFinal, otherReserve, otherCancel, frames⟩ := allocated_receiver_cancel_pending config initialized owner
    ty element request origin knownCount before allocated id ambient types live regions pending world elementType created
  have sameReserved : otherReserved = reserved := (ConstructionResult.ok.inj (otherReserve.symm.trans reserve)).2
  subst otherReserved
  have sameFinal : otherFinal = final := (ConstructionResult.ok.inj (otherCancel.symm.trans cancel)).2
  subst otherFinal
  exact ⟨reserved, final, reserve, cancel, rooted, regionsSafe, frames⟩

#print axioms allocated_receiver_cancel_protected

end Goose.Proofs.ConstructionAcceptedExecution
