import Goose.Proofs.ConstructionExitEvaluationHistoryFrames
import Goose.Proofs.ConstructionExitProducedFrame
import Goose.Proofs.ConstructionExitByteReservation

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem accepted_byte_evaluationHistory_returned (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (bytes : List UInt8) (origin : OriginId) (id count : Nat)
    (before after : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (history : EvaluationHistoryCoverage before ambient pending)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (receiver : ready.destination.use = .receiver) (fits : count + bytes.length < 2 ^ 32)
    (current : destinationCurrent before.construction id = .ok id)
    (built : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    let frame : PendingCarrierFrame := ⟨[.construct id], [.completed id]⟩
    EvaluationHistoryCoverage after (.returned frame.carriers :: ambient) (frame :: pending) ∧
      CarriersLandingReady after frame.channels frame.carriers ∧
      (∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout after carrier) ∧
      landCarriersInto origin frame.channels frame.carriers after = .ok () after := by
  have tickets := buildExpr_bytes_tickets fuel config environment id (.varr (.int .u8)) bytes origin before after
    ready.destination count world.ownership.source current ready.present ready.opened built
  have prior : EvaluationHistoryCoverage after ambient pending := by
    constructor
    · apply reservationReferencesBounded_mono before.construction after.construction ambient _ history.1
      rw [tickets]
      exact Nat.le_refl _
    · exact history.2
  have produced := accepted_byte_receiver_produced_frame fuel config initialized environment bytes origin id count
    before after ambient types live regions pending world ready packed request receiver fits current built history.2
  exact ⟨evaluationHistoryCoverage_returned after ambient pending [.construct id] [.completed id] prior,
    produced.1, produced.2.1, produced.2.2.1⟩

#print axioms accepted_byte_evaluationHistory_returned

end Goose.Proofs.ConstructionAcceptedExecution
