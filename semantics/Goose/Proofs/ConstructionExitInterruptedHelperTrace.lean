import Goose.Proofs.ConstructionExitInterruptedInnerTrace

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 4000000

namespace Goose.Proofs.ConstructionAcceptedExecution.InterruptedTrace
open Goose.Construct
open Goose.Proofs.ExitExecution
open Goose.Proofs.ExitExecutionChecks
open Goose.Proofs.ConstructionAcceptedExecution

def interruptOperand : Expr := .arrLit array [.lit .u8 1,
  .ifE (.bool true) (.mk 2 [.brk 0] none) (.mk 3 [] (some (.lit .u8 2))) 0] 0

def interruptLoopBody : Block := .mk 1 [.returnFrom 0 [interruptOperand] 0] none

def interruptHelper : Impl := ⟨"helper", #[], #[], #[],
  .mk 0 [.while (.bool true) interruptLoopBody 0, .returnFrom 0 [.bytes array [66] 0] 0] none,
  .known ⟨[], [], [], [], [], [], [0], [0], false, false⟩⟩

theorem interrupt_helper_loop_reached :
    ExitReached 44 interruptConfig
      (.statement 16 recursiveCheckpointSource (.while (.bool true) interruptLoopBody 0)) recursiveDirectCheckpoint := by
  have implementation : interruptConfig.module.impls[recursiveOuterActivation.implementation]? = some interruptBuilderImpl := by cbv
  have body : ExitReached 44 interruptConfig
      (.activationBody 27 recursiveOuterActivation [(0, .int .i64 0)] interruptedReturnBuilderBody) recursiveOuterEntered :=
    .call interrupt_outer_activation_reached (.activationBody 27 recursiveOuterActivation [(0, .int .i64 0)] interruptedReturnBuilderBody 0 recursiveOuterEntered interruptBuilderImpl implementation)
  have scope : ExitReached 44 interruptConfig
      (.activationScope 26 recursiveOuterActivation [(0, .int .i64 0)] interruptedReturnBuilderBody) recursiveOuterEntered :=
    .call body (.activationScope 26 recursiveOuterActivation [(0, .int .i64 0)] interruptedReturnBuilderBody recursiveOuterEntered)
  have binding : bindAll recursiveOuterActivation.act recursiveOuterEntered.nextScope [(0, .int .i64 0)] { recursiveOuterEntered with
      nextScope := recursiveOuterEntered.nextScope + 1
      activations := recursiveOuterEntered.activations.map (fun current => if current.act == recursiveOuterActivation.act then
        { current with scopes := (0, recursiveOuterEntered.nextScope) :: recursiveOuterActivation.scopes } else current) } =
      .ok () recursiveBeforeBranch := by cbv
  have environment : { recursiveOuterActivation with scopes :=
      (0, recursiveOuterEntered.nextScope) :: recursiveOuterActivation.scopes } = recursiveCheckpointTarget := by cbv
  have statements : ExitReached 44 interruptConfig
      (.statements 26 recursiveCheckpointTarget [.ifS recursiveBranchCondition recursiveBranchBlock (some recursiveOuterElse) 0,
        .retValues [.bytes array [68] 0] 0]) recursiveBeforeBranch := by
    have edge := ExitCallSite.activationStatements (config := interruptConfig) 26 recursiveOuterActivation
      [(0, .int .i64 0)] 0 [.ifS recursiveBranchCondition recursiveBranchBlock (some recursiveOuterElse) 0,
        .retValues [.bytes array [68] 0] 0] none recursiveOuterEntered recursiveBeforeBranch binding
    rw [environment] at edge
    exact .call scope (by simpa [interruptedReturnBuilderBody, recursiveBranchCondition, recursiveBranchBlock, recursiveOuterElse] using edge)
  have branch : ExitReached 44 interruptConfig
      (.statement 25 recursiveCheckpointTarget (.ifS recursiveBranchCondition recursiveBranchBlock (some recursiveOuterElse) 0)) recursiveBeforeBranch :=
    .call statements (.statementsHead 25 recursiveCheckpointTarget _ _ recursiveBeforeBranch)
  have condition : ((do expectBool (← evalValue 24 interruptConfig recursiveCheckpointTarget recursiveBranchCondition)) : EvalM Bool)
      recursiveBeforeBranch = .ok true recursiveBeforeBranch := by cbv
  have block : ExitReached 44 interruptConfig (.block 24 recursiveCheckpointTarget [] [] recursiveBranchBlock) recursiveBeforeBranch :=
    .call branch (.statements (.ifYes 24 recursiveCheckpointTarget recursiveBranchCondition recursiveBranchBlock
      (some recursiveOuterElse) 0 recursiveBeforeBranch recursiveBeforeBranch condition))
  have binding : bindAll recursiveCheckpointTarget.act recursiveBeforeBranch.nextScope []
      { recursiveBeforeBranch with nextScope := recursiveBeforeBranch.nextScope + 1 } = .ok () recursiveBeforeHelper := by cbv
  have environment : { recursiveCheckpointTarget with scopes :=
      (1, recursiveBeforeBranch.nextScope) :: recursiveCheckpointTarget.scopes } = recursiveCallerScope := by cbv
  have statements : ExitReached 44 interruptConfig
      (.statements 23 recursiveCallerScope [.expr (.call 2 [] 0) 0]) recursiveBeforeHelper := by
    have edge := ExitCallSite.blockStatements (config := interruptConfig) 23 recursiveCheckpointTarget [] [] 1
      [.expr (.call 2 [] 0) 0] none recursiveBeforeBranch recursiveBeforeHelper binding
    rw [environment] at edge
    exact .call block (by simpa [recursiveBranchBlock] using edge)
  have statement : ExitReached 44 interruptConfig (.statement 22 recursiveCallerScope (.expr (.call 2 [] 0) 0)) recursiveBeforeHelper :=
    .call statements (.statementsHead 22 recursiveCallerScope _ [] recursiveBeforeHelper)
  have value : ExitReached 44 interruptConfig (.value 21 recursiveCallerScope (.call 2 [] 0)) recursiveBeforeHelper :=
    .call statement (.statements (.expression 21 recursiveCallerScope (.call 2 [] 0) 0 recursiveBeforeHelper))
  have lookup : getImplementation interruptConfig 2 recursiveBeforeHelper = .ok (2, interruptHelper) recursiveBeforeHelper := by cbv
  have channels : channelsFor interruptConfig.layout recursiveCallerScope.act interruptHelper.results.toList 0 recursiveBeforeHelper =
      .ok [] recursiveBeforeHelper := by cbv
  have call : ExitReached 44 interruptConfig (.call 20 recursiveCallerScope 2 [] [] 0) recursiveBeforeHelper :=
    .call value (.values (.valueCall lookup channels))
  have receiving : CallArgumentPrefix interruptConfig 2 [] 0 recursiveBeforeHelper 2 interruptHelper [] recursiveBeforeHelper :=
    .actual recursiveBeforeHelper recursiveBeforeHelper recursiveBeforeHelper 2 interruptHelper [] lookup (by cbv) (by cbv)
  have arguments : evalArguments 19 interruptConfig recursiveCallerScope interruptHelper.vars interruptHelper.params.toList [] recursiveBeforeHelper =
      .ok [] recursiveBeforeHelper := by cbv
  have depth : recursiveBeforeHelper.activations.length < Goose.Core.maxCallDepth := by cbv
  have callPrefix := CallActivationPrefix.actual recursiveBeforeHelper recursiveBeforeHelper recursiveBeforeHelper recursiveBeforeHelper
    2 interruptHelper [] [] [] receiving arguments rfl depth
  have entered : { recursiveBeforeHelper with
      nextAct := recursiveBeforeHelper.nextAct + 1
      activations := ⟨2, recursiveBeforeHelper.nextAct, interruptHelper.vars, [], []⟩ :: recursiveBeforeHelper.activations } = recursiveHelperEntered := by cbv
  rw [entered] at callPrefix
  have nextAct : recursiveBeforeHelper.nextAct = 3 := by cbv
  rw [nextAct] at callPrefix
  have activation : ExitReached 44 interruptConfig (.activation 19 recursiveHelperActivation [] interruptHelper.body 0) recursiveHelperEntered :=
    .call call (.callActivation 19 recursiveCallerScope 2 [] [] 0 recursiveBeforeHelper recursiveHelperEntered recursiveHelperActivation []
      interruptHelper.body (by simpa [recursiveHelperActivation, interruptHelper] using callPrefix))
  have implementation : interruptConfig.module.impls[recursiveHelperActivation.implementation]? = some interruptHelper := by cbv
  have body : ExitReached 44 interruptConfig (.activationBody 18 recursiveHelperActivation [] interruptHelper.body) recursiveHelperEntered :=
    .call activation (.activationBody 18 recursiveHelperActivation [] interruptHelper.body 0 recursiveHelperEntered interruptHelper implementation)
  have scope : ExitReached 44 interruptConfig (.activationScope 17 recursiveHelperActivation [] interruptHelper.body) recursiveHelperEntered :=
    .call body (.activationScope 17 recursiveHelperActivation [] interruptHelper.body recursiveHelperEntered)
  have binding := recursive_checkpoint_helper_binding
  have environment : { recursiveHelperActivation with scopes :=
      (0, recursiveHelperEntered.nextScope) :: recursiveHelperActivation.scopes } = recursiveCheckpointSource := by cbv
  have statements : ExitReached 44 interruptConfig (.statements 17 recursiveCheckpointSource
      [.while (.bool true) interruptLoopBody 0, .returnFrom 0 [.bytes array [66] 0] 0]) recursiveDirectCheckpoint := by
    have edge := ExitCallSite.activationStatements (config := interruptConfig) 17 recursiveHelperActivation [] 0
      [.while (.bool true) interruptLoopBody 0, .returnFrom 0 [.bytes array [66] 0] 0] none
      recursiveHelperEntered recursiveDirectCheckpoint binding
    rw [environment] at edge
    exact .call scope (by simpa [interruptHelper] using edge)
  exact .call statements (.statementsHead 16 recursiveCheckpointSource _ _ recursiveDirectCheckpoint)

#print axioms interrupt_helper_loop_reached

end Goose.Proofs.ConstructionAcceptedExecution.InterruptedTrace
