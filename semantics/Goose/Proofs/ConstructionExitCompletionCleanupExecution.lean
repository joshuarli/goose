import Goose.Proofs.ConstructionExitWaitingWorld
import Goose.Proofs.ConstructionExitEvaluationHistoryMixedCleanup
import Goose.Proofs.ConstructionExitFrameRelease

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem completion_byte_with_completion_channels (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (bytes : List UInt8) (origin : OriginId)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (history : EvaluationHistoryCoverage before ambient pending)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (receiver : ready.destination.use = .receiver) (packed : ready.destination.layout = .packed)
    (adaptation : ready.destination.adaptation = none) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id) (fits : bytes.length < 2 ^ 32) :
    let token := before.construction.exitReservations.size
    ∃ after : ExecutionState,
      let cleaned := { after with construction := { after.construction with
        exitReservations := after.construction.exitReservations.set! token .released } }
      withCompletionChannels [.construct id] origin
        (fun channels => evalProduce (fuel + 2) config environment channels (.bytes (.varr (.int .u8)) bytes origin)) before =
        .ok [.completed id] cleaned ∧
      EvaluationHistoryLifecycle cleaned (.returned [.completed id] :: .completionChannels [token] [] [] :: ambient)
        (⟨[.completion token], [.completed id]⟩ :: pending) := by
  let token := before.construction.exitReservations.size
  let waited := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push (.waiting id) } }
  obtain ⟨after, wait, evaluated, tracked, paired, backed, landed⟩ :=
    completion_byte_receiver_history fuel config initialized environment before ambient types live regions pending id bytes origin
      world history ready receiver packed adaptation request current fits
  change waitExitDestination id before.construction = .ok token waited.construction at wait
  change evalProduce (fuel + 2) config environment [.completion token] (.bytes (.varr (.int .u8)) bytes origin) waited =
    .ok [.completed id] after at evaluated
  have evaluatedAt : evalProduce (fuel + 2) config environment [.completion token] (.bytes (.varr (.int .u8)) bytes origin)
      { before with construction := waited.construction } = .ok [.completed id] after := evaluated
  have pairedOne : CarrierLandingReady after (.completion token) (.completed id) := paired.pairs _ _ (by simp [token])
  cases pairedOne with
  | completion _ incoming selected _ role snapshot ticket receiving =>
    let cleaned := { after with construction := { after.construction with
      exitReservations := after.construction.exitReservations.set! token .released } }
    have released := releaseExitReservation_active after.construction token role incoming selected snapshot ticket
    have lifecycle : ReservationLifecycleInvariant after.construction := by
      have valid := evaluator_fixed_history_coverage (fuel + 2) config .carriers _
        (.produce environment [.completion token] (.bytes (.varr (.int .u8)) bytes origin)) waited
        (.completionChannels [token] [] [] :: ambient) pending
      have worldWait := waitExitDestination_acceptedWorld config initialized before ambient types live regions pending id world history.1
      have coverage : EvaluationHistoryCoverage waited (.completionChannels [token] [] [] :: ambient) pending := by
        refine ⟨(wait_completion_references_bounded before.construction ambient id [] [] history.1).2, ?_⟩
        intro old member
        simp only [OwnershipAmbient.retained, List.flatMap_cons, OwnershipAmbientFrame.carriers, List.nil_append] at member
        exact history.2 old member
      have result := valid ⟨worldWait.2.ownership.source.structural.1.1, coverage⟩
      simpa only [evaluated, Goose.Proofs.Exit.stepState] using result.1
    have afterTracked : EvaluationHistoryLifecycle after (.returned [.completed id] :: .completionChannels [token] [] [] :: ambient)
        (⟨[.completion token], [.completed id]⟩ :: pending) := ⟨lifecycle, tracked⟩
    have cleanupHistory := evaluationHistoryLifecycle_release origin token
      (.returned [.completed id] :: .completionChannels [token] [] [] :: ambient)
      (⟨[.completion token], [.completed id]⟩ :: pending) after afterTracked
    refine ⟨after, ?_, ?_⟩
    · simp only [withCompletionChannels, completionChannelSetup, List.mapM_cons, List.mapM_nil, liftConstruction, wait, bind, pure,
        List.map_cons, List.map_nil, List.filterMap_cons, List.filterMap_nil, evaluatedAt, materializeOwnedCarriers,
        List.reverse_cons, List.reverse_nil, List.nil_append, List.forIn_cons, List.forIn_nil,
        Bool.false_eq_true, ↓reduceIte, released]
      rfl
    · simpa only [liftConstruction, released, Goose.Proofs.Exit.stepState] using cleanupHistory

#print axioms completion_byte_with_completion_channels

end Goose.Proofs.ConstructionAcceptedExecution
