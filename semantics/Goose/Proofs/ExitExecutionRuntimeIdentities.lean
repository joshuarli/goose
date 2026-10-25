import Goose.Proofs.ExitExecution
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationFrames
import Goose.Proofs.OwnershipRuntimeIdentitiesPreservation
import Goose.Proofs.OwnershipEvaluationActions

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Proofs.ExitExecution Goose.Proofs.ConstructionDelivery

private theorem preservesBreakIdentities_of_frame (action : EvalM α)
    (frame : BreakFrameAction action) : PreservesOwnershipBreakIdentities action := by
  intro state valid
  have checked := frame state valid.bounded
  cases evaluated : action state <;> rw [evaluated] at checked
  all_goals change BreakStackFrame state _ at checked
  all_goals exact ⟨by simpa only [Goose.Proofs.Exit.stepState, checked.stack] using valid.distinct, checked.bounded valid.bounded⟩

theorem evaluation_runtimeIdentities (fuel : Nat) (config : EvalConfig)
    {shape : OwnershipResultShape α} {action : EvalM α}
    (selected : OwnershipEvaluationAction fuel config shape action) :
    PreservesOwnershipRuntimeIdentities action := by
  have fresh := evaluation_preservesFresh fuel config
  have frames := evaluationBreakFrames fuel config
  apply preservesOwnershipRuntimeIdentities_of_components
  · cases selected
    all_goals first
      | exact fresh.value _ _
      | exact fresh.bound _ _ _ _
      | exact fresh.place _ _
      | exact fresh.view _ _
      | exact fresh.produce _ _ _
      | exact fresh.operands _ _ _
      | exact fresh.build _ _ _
      | exact fresh.element _ _ _ _
      | exact fresh.arguments _ _ _ _
      | exact fresh.call _ _ _ _ _
      | exact fresh.activation _ _ _ _
      | exact fresh.activationBody _ _ _
      | exact fresh.resultBlock _ _ _
      | exact fresh.resultBlockWith _ _ _ _
      | exact fresh.block _ _ _ _
      | exact fresh.statements _ _
      | exact fresh.statement _ _
      | exact fresh.printArgument _ _
      | exact fresh.whileLoop _ _ _
      | exact fresh.rangeLoop _ _ _ _ _ _
      | exact fresh.eachLoop _ _ _ _ _ _ _
      | exact fresh.loop _ _ _
      | exact fresh.push _ _ _ _
  · apply preservesBreakIdentities_of_frame
    cases selected
    all_goals first
      | exact frames.value _ _
      | exact frames.bound _ _ _ _
      | exact frames.place _ _
      | exact frames.view _ _
      | exact frames.produce _ _ _
      | exact frames.operands _ _ _
      | exact frames.build _ _ _
      | exact frames.element _ _ _ _
      | exact frames.arguments _ _ _ _
      | exact frames.call _ _ _ _ _
      | exact frames.activation _ _ _ _
      | exact frames.activationBody _ _ _
      | exact frames.resultBlock _ _ _
      | exact frames.resultBlockWith _ _ _ _
      | exact frames.block _ _ _ _
      | exact frames.statements _ _
      | exact frames.statement _ _
      | exact frames.printArgument _ _
      | exact frames.whileLoop _ _ _
      | exact frames.rangeLoop _ _ _ _ _ _
      | exact frames.eachLoop _ _ _ _ _ _ _
      | exact frames.loop _ _ _
      | exact frames.push _ _ _ _

theorem runModule_preservesRuntimeIdentities (fuel : Nat) (config : EvalConfig) :
    PreservesOwnershipRuntimeIdentities (runModule fuel config) :=
  preservesOwnershipRuntimeIdentities_of_components _ (runModule_preservesFresh fuel config)
    (preservesBreakIdentities_of_frame _ (runModule_breakFrame fuel config))

theorem runModule_runtimeIdentities_initial (fuel : Nat) (config : EvalConfig) :
    OwnershipRuntimeIdentities (Goose.Proofs.Exit.stepState (runModule fuel config .initial)) :=
  runModule_preservesRuntimeIdentities fuel config .initial initial_ownershipRuntimeIdentities

#print axioms evaluation_runtimeIdentities
#print axioms runModule_runtimeIdentities_initial

end Goose.Proofs.ConstructionExecutionOwnership
