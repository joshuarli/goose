import Goose.Proofs.ConstructionExitEvaluationHistoryMixedCompletion

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem completion_operands_release_all_outcomes (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (channels : List Channel) (expressions : List Expr) (origin : OriginId)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (history : EvaluationHistoryCoverage before ambient pending) :
    let token := before.construction.exitReservations.size
    let waited := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.waiting id) } }
    let frame := OwnershipAmbientFrame.completionChannels [token] [] []
    let release := liftConstruction origin (releaseExitReservation token)
    waitExitDestination id before.construction = .ok token waited.construction ∧
    match evalOperands fuel config environment channels expressions waited with
    | .ok carriers state | .escape _ carriers state | .jump _ (.breakValue carriers) state =>
        EvaluationHistoryLifecycle (Goose.Proofs.Exit.stepState (release state))
          (.returned carriers :: frame :: ambient) (⟨channels, carriers⟩ :: pending)
    | .stop _ state | .jump _ .continueLoop state =>
        EvaluationHistoryLifecycle (Goose.Proofs.Exit.stepState (release state)) (frame :: ambient) pending := by
  let token := before.construction.exitReservations.size
  let waited := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push (.waiting id) } }
  have result := completion_mixed_operands_all_outcomes fuel config initialized environment before ambient types live regions pending
    id channels expressions world history
  refine ⟨result.1, ?_⟩
  have tracked := result.2
  change EvaluationHistoryLifecycleOutcome .carriers channels (.completionChannels [token] [] [] :: ambient) pending
    (evalOperands fuel config environment channels expressions waited) at tracked
  cases evaluated : evalOperands fuel config environment channels expressions waited with
  | ok carriers state | escape _ carriers state =>
    simp only [evaluated, EvaluationHistoryLifecycleOutcome] at tracked ⊢
    exact evaluationHistoryLifecycle_release origin token _ _ state tracked
  | stop reason state =>
    simp only [evaluated, EvaluationHistoryLifecycleOutcome] at tracked ⊢
    exact evaluationHistoryLifecycle_release origin token _ _ state tracked
  | jump target kind state =>
    cases kind with
    | breakValue carriers =>
      simp only [evaluated, EvaluationHistoryLifecycleOutcome] at tracked ⊢
      exact evaluationHistoryLifecycle_release origin token _ _ state tracked
    | continueLoop =>
      simp only [evaluated, EvaluationHistoryLifecycleOutcome] at tracked ⊢
      exact evaluationHistoryLifecycle_release origin token _ _ state tracked

#print axioms completion_operands_release_all_outcomes

end Goose.Proofs.ConstructionAcceptedExecution
