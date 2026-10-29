import Goose.Proofs.ConstructionExitWrittenCancelPending

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem allocated_byte_write_cancel_lifecycle (config : EvalConfig) (initialized : Nat) (owner : ActId)
    (origin : OriginId) (knownCount : Option Nat) (byte : UInt8)
    (before allocated : ExecutionState) (id : Nat) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout owner (.varr (.int .u8)) .value origin none knownCount before = .ok id allocated) :
    ∃ reserved written final,
      reserveExitDestination id .newValue allocated.construction = .ok (allocated.construction.exitReservations.size, id) reserved ∧
      writeElement id ⟨#[byte]⟩ reserved = .ok () written ∧
      (do cancelExitReservation allocated.construction.exitReservations.size []
          releaseExitReservation allocated.construction.exitReservations.size) written = .ok () final ∧
      ReservationLifecycleInvariant final ∧
      RootedBackingObservations config.layout { allocated with construction := final } live (storageExtent before) ∧
      (∀ region ∈ regions, ReceivingProtection config.layout { allocated with construction := final } live region) ∧
      ∀ frame ∈ pending, CarriersLandingReady { allocated with construction := final } frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout { allocated with construction := final } carrier := by
  obtain ⟨reserved, written, final, reserve, write, cancel, rooted, _, _⟩ :=
    allocated_byte_write_cancel_frame config initialized owner origin knownCount byte before allocated id ambient types live regions pending world created
  obtain ⟨r2, w2, f2, reserve2, write2, cancel2, regionFrames⟩ :=
    allocated_byte_write_cancel_regions config initialized owner origin knownCount byte before allocated id ambient types live regions pending world created
  have same : r2 = reserved := (ConstructionResult.ok.inj (reserve2.symm.trans reserve)).2
  subst r2
  have same : w2 = written := (ConstructionResult.ok.inj (write2.symm.trans write)).2
  subst w2
  have same : f2 = final := (ConstructionResult.ok.inj (cancel2.symm.trans cancel)).2
  subst f2
  obtain ⟨r2, w2, f2, reserve2, write2, cancel2, pendingFrames⟩ :=
    allocated_byte_write_cancel_pending config initialized owner origin knownCount byte before allocated id ambient types live regions pending world created
  have same : r2 = reserved := (ConstructionResult.ok.inj (reserve2.symm.trans reserve)).2
  subst r2
  have same : w2 = written := (ConstructionResult.ok.inj (write2.symm.trans write)).2
  subst w2
  have same : f2 = final := (ConstructionResult.ok.inj (cancel2.symm.trans cancel)).2
  subst f2
  have allocatedWorld := newDestination_acceptedWorld config owner (.varr (.int .u8)) .value origin knownCount initialized before allocated id
    ambient types live regions pending world created
  have reservedLife := reserveExitDestination_reservation_lifecycle id .newValue allocated.construction allocatedWorld.ownership.source.structural.1.1
  rw [reserve] at reservedLife
  simp only [ConstructionResult.finalState] at reservedLife
  have metadata := writeElement_reservation_frame id ⟨#[byte]⟩ reserved reservedLife.1
  rw [write] at metadata
  simp only [ConstructionResult.finalState] at metadata
  have destLife := writeElement_destination_lifecycle_invariant id ⟨#[byte]⟩ reserved reservedLife.1
  rw [write] at destLife
  simp only [ConstructionResult.finalState] at destLife
  have writtenLife : ReservationLifecycleInvariant written :=
    ⟨destLife, destinationReservationStateValid_frame reserved written metadata reservedLife.2⟩
  have cancelLife := cancelExitReservation_lifecycle allocated.construction.exitReservations.size [] written writtenLife
  cases step : cancelExitReservation allocated.construction.exitReservations.size [] written with
  | fault reason stopped => simp [bind, step] at cancel
  | ok value middle =>
    cases value
    simp only [step, ConstructionResult.finalState] at cancelLife
    have releaseLife := releaseExitReservation_lifecycle middle allocated.construction.exitReservations.size cancelLife
    have release : releaseExitReservation allocated.construction.exitReservations.size middle = .ok () final := by
      simpa only [bind, step] using cancel
    rw [release] at releaseLife
    simp only [ConstructionResult.finalState] at releaseLife
    exact ⟨reserved, written, final, reserve, write, cancel, releaseLife, rooted, regionFrames, pendingFrames⟩

#print axioms allocated_byte_write_cancel_lifecycle

end Goose.Proofs.ConstructionAcceptedExecution
