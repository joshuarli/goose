import Goose.Proofs.ConstructionExitDirectHistory
import Goose.Proofs.ConstructionExitProducedFrame

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem direct_byte_cleanup_history_and_coverage (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (bytes : List UInt8) (origin : OriginId) (before : ExecutionState) (id : Nat)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (source : OwnershipSourceState before.construction) (ambient : OwnershipAmbient)
    (history : ReservationReferencesBounded before.construction ambient) (pending : List PendingCarrierFrame)
    (coverage : ∀ old, .completed old ∈ ambient.retained → ∃ frame ∈ pending, .completed old ∈ frame.carriers)
    (receiver : ready.destination.use = .receiver) (packed : ready.destination.layout = .packed)
    (adaptation : ready.destination.adaptation = none) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id) (fits : bytes.length < 2 ^ 32) :
    let token := before.construction.exitReservations.size
    let reserved := { before.construction with exitReservations := before.construction.exitReservations.push (.active .fresh id id ready.destination) }
    let prepared := { before with construction := reserved }
    let frame : PendingCarrierFrame := ⟨[.construct id], [.completed id]⟩
    ∃ after cleaned : ExecutionState,
      reserveExitDestination id .newValue before.construction = .ok (token, id) reserved ∧
      buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) prepared = .ok () after ∧
      ReservationReferencesBounded after.construction (.exitChannels [token] frame.channels frame.carriers :: ambient) ∧
      exitChannelCleanupBorrowed origin [] [token] false frame.carriers after = .ok () cleaned ∧
      ReservationReferencesBounded cleaned.construction ambient ∧
      (∀ retained, .completed retained ∈ OwnershipAmbient.retained (.returned frame.carriers :: ambient) →
        ∃ prior ∈ frame :: pending, .completed retained ∈ prior.carriers) := by
  obtain ⟨after, cleaned, reservation, built, bounded, cleanup, oldBounded⟩ :=
    direct_byte_reservation_history fuel config environment bytes origin before id ready source ambient history
      receiver packed adaptation request current fits
  refine ⟨after, cleaned, reservation, built, bounded, cleanup, oldBounded, ?_⟩
  intro retained member
  simp only [OwnershipAmbient.retained, List.flatMap_cons, OwnershipAmbientFrame.carriers,
    List.mem_append, List.mem_singleton, Goose.Construct.Carrier.completed.injEq] at member
  rcases member with same | prior
  · subst retained
    exact ⟨⟨[.construct id], [.completed id]⟩, by simp, by simp⟩
  · obtain ⟨old, present, kept⟩ := coverage retained prior
    exact ⟨old, List.mem_cons_of_mem _ present, kept⟩

#print axioms direct_byte_cleanup_history_and_coverage

end Goose.Proofs.ConstructionAcceptedExecution
