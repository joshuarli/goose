import Goose.Proofs.ConstructionExitCheckpointHandler
import Goose.Proofs.ConstructionExitCheckpointContext
import Goose.Proofs.ExitExecutionPathContext

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 4000000

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ExitExecution
open Goose.Proofs.ExitExecutionChecks

theorem recursive_helper_call_reaches_return {rootFuel : Nat}
    (reached : ExitReached rootFuel recursiveCheckpointConfig
      (.call 8 recursiveCallerScope 2 [] [] 0) recursiveBeforeHelper) :
    ExitReached rootFuel recursiveCheckpointConfig
      (.statement 4 recursiveCheckpointSource (.returnFrom 0 [.bytes array [66] 0] 0)) recursiveDirectCheckpoint := by
  have callPrefix := recursive_checkpoint_call_prefix 6
  have activation : ExitReached rootFuel recursiveCheckpointConfig
      (.activation 7 recursiveHelperActivation [] recursiveHelper.body 0) recursiveHelperEntered :=
    .call reached (.callActivation 7 recursiveCallerScope 2 [] [] 0 recursiveBeforeHelper recursiveHelperEntered
      recursiveHelperActivation [] recursiveHelper.body callPrefix)
  have implementation : recursiveCheckpointConfig.module.impls[recursiveHelperActivation.implementation]? = some recursiveHelper := by cbv
  have body : ExitReached rootFuel recursiveCheckpointConfig
      (.activationBody 6 recursiveHelperActivation [] recursiveHelper.body) recursiveHelperEntered :=
    .call activation (.activationBody 6 recursiveHelperActivation [] recursiveHelper.body 0 recursiveHelperEntered recursiveHelper implementation)
  have scope : ExitReached rootFuel recursiveCheckpointConfig
      (.activationScope 5 recursiveHelperActivation [] recursiveHelper.body) recursiveHelperEntered :=
    .call body (.activationScope 5 recursiveHelperActivation [] recursiveHelper.body recursiveHelperEntered)
  have environment : { recursiveHelperActivation with scopes :=
      (0, recursiveHelperEntered.nextScope) :: recursiveHelperActivation.scopes } = recursiveCheckpointSource := by cbv
  have statements : ExitReached rootFuel recursiveCheckpointConfig
      (.statements 5 recursiveCheckpointSource [.returnFrom 0 [.bytes array [66] 0] 0]) recursiveDirectCheckpoint := by
    have edge := ExitCallSite.activationStatements (config := recursiveCheckpointConfig) 5 recursiveHelperActivation [] 0
      [.returnFrom 0 [.bytes array [66] 0] 0] none recursiveHelperEntered recursiveDirectCheckpoint recursive_checkpoint_helper_binding
    rw [environment] at edge
    exact .call scope (by simpa [recursiveHelper] using edge)
  exact .call statements (.statementsHead 4 recursiveCheckpointSource (.returnFrom 0 [.bytes array [66] 0] 0) [] recursiveDirectCheckpoint)

theorem recursive_branch_reaches_return {rootFuel : Nat}
    (reached : ExitReached rootFuel recursiveCheckpointConfig
      (.statement 13 recursiveCheckpointTarget
        (.ifS recursiveBranchCondition recursiveBranchBlock (some recursiveOuterElse) 0)) recursiveBeforeBranch) :
    ExitReached rootFuel recursiveCheckpointConfig
      (.statement 4 recursiveCheckpointSource (.returnFrom 0 [.bytes array [66] 0] 0)) recursiveDirectCheckpoint := by
  have condition : ((do expectBool (← evalValue 12 recursiveCheckpointConfig recursiveCheckpointTarget recursiveBranchCondition)) : EvalM Bool)
      recursiveBeforeBranch = .ok true recursiveBeforeBranch := by cbv
  have block : ExitReached rootFuel recursiveCheckpointConfig
      (.block 12 recursiveCheckpointTarget [] [] recursiveBranchBlock) recursiveBeforeBranch :=
    .call reached (.statements (.ifYes 12 recursiveCheckpointTarget recursiveBranchCondition recursiveBranchBlock
      (some recursiveOuterElse) 0 recursiveBeforeBranch recursiveBeforeBranch condition))
  have binding : bindAll recursiveCheckpointTarget.act recursiveBeforeBranch.nextScope []
      { recursiveBeforeBranch with nextScope := recursiveBeforeBranch.nextScope + 1 } = .ok () recursiveBeforeHelper := by cbv
  have environment : { recursiveCheckpointTarget with scopes :=
      (1, recursiveBeforeBranch.nextScope) :: recursiveCheckpointTarget.scopes } = recursiveCallerScope := by cbv
  have statements : ExitReached rootFuel recursiveCheckpointConfig
      (.statements 11 recursiveCallerScope [.expr (.call 2 [] 0) 0]) recursiveBeforeHelper := by
    have edge := ExitCallSite.blockStatements (config := recursiveCheckpointConfig) 11 recursiveCheckpointTarget [] [] 1
      [.expr (.call 2 [] 0) 0] none recursiveBeforeBranch recursiveBeforeHelper binding
    rw [environment] at edge
    exact .call block (by simpa [recursiveBranchBlock] using edge)
  have statement : ExitReached rootFuel recursiveCheckpointConfig
      (.statement 10 recursiveCallerScope (.expr (.call 2 [] 0) 0)) recursiveBeforeHelper :=
    .call statements (.statementsHead 10 recursiveCallerScope (.expr (.call 2 [] 0) 0) [] recursiveBeforeHelper)
  have value : ExitReached rootFuel recursiveCheckpointConfig
      (.value 9 recursiveCallerScope (.call 2 [] 0)) recursiveBeforeHelper :=
    .call statement (.statements (.expression 9 recursiveCallerScope (.call 2 [] 0) 0 recursiveBeforeHelper))
  have lookup : getImplementation recursiveCheckpointConfig 2 recursiveBeforeHelper = .ok (2, recursiveHelper) recursiveBeforeHelper := by cbv
  have channels : channelsFor recursiveCheckpointConfig.layout recursiveCallerScope.act recursiveHelper.results.toList 0 recursiveBeforeHelper =
      .ok [] recursiveBeforeHelper := by cbv
  have call : ExitReached rootFuel recursiveCheckpointConfig
      (.call 8 recursiveCallerScope 2 [] [] 0) recursiveBeforeHelper :=
    .call value (.values (.valueCall lookup channels))
  exact recursive_helper_call_reaches_return call

theorem recursive_outer_activation_reaches_return {rootFuel : Nat}
    (reached : ExitReached rootFuel recursiveCheckpointConfig
      (.activation 16 recursiveOuterActivation [(0, .int .i64 0)] recursiveOuterBody 0) recursiveOuterEntered) :
    ExitReached rootFuel recursiveCheckpointConfig
      (.statement 4 recursiveCheckpointSource (.returnFrom 0 [.bytes array [66] 0] 0)) recursiveDirectCheckpoint := by
  have implementation : recursiveCheckpointConfig.module.impls[recursiveOuterActivation.implementation]? =
      some ⟨"builder", #[⟨0, .byValue⟩], #[⟨array, .value, none⟩], recursiveOuterActivation.vars, recursiveOuterBody,
        .known ⟨[], [], [], [], [], [0], [], [], true, true⟩⟩ := by cbv
  have body : ExitReached rootFuel recursiveCheckpointConfig
      (.activationBody 15 recursiveOuterActivation [(0, .int .i64 0)] recursiveOuterBody) recursiveOuterEntered :=
    .call reached (.activationBody 15 recursiveOuterActivation [(0, .int .i64 0)] recursiveOuterBody 0 recursiveOuterEntered _ implementation)
  have scope : ExitReached rootFuel recursiveCheckpointConfig
      (.activationScope 14 recursiveOuterActivation [(0, .int .i64 0)] recursiveOuterBody) recursiveOuterEntered :=
    .call body (.activationScope 14 recursiveOuterActivation [(0, .int .i64 0)] recursiveOuterBody recursiveOuterEntered)
  have binding : bindAll recursiveOuterActivation.act recursiveOuterEntered.nextScope [(0, .int .i64 0)] { recursiveOuterEntered with
      nextScope := recursiveOuterEntered.nextScope + 1
      activations := recursiveOuterEntered.activations.map (fun current => if current.act == recursiveOuterActivation.act then
        { current with scopes := (0, recursiveOuterEntered.nextScope) :: recursiveOuterActivation.scopes } else current) } =
      .ok () recursiveBeforeBranch := by cbv
  have environment : { recursiveOuterActivation with scopes :=
      (0, recursiveOuterEntered.nextScope) :: recursiveOuterActivation.scopes } = recursiveCheckpointTarget := by cbv
  have statements : ExitReached rootFuel recursiveCheckpointConfig
      (.statements 14 recursiveCheckpointTarget [.ifS recursiveBranchCondition recursiveBranchBlock (some recursiveOuterElse) 0])
      recursiveBeforeBranch := by
    have edge := ExitCallSite.activationStatements (config := recursiveCheckpointConfig) 14 recursiveOuterActivation
      [(0, .int .i64 0)] 0 [.ifS recursiveBranchCondition recursiveBranchBlock (some recursiveOuterElse) 0] none
      recursiveOuterEntered recursiveBeforeBranch binding
    rw [environment] at edge
    exact .call scope (by simpa [recursiveOuterBody] using edge)
  have branch : ExitReached rootFuel recursiveCheckpointConfig
      (.statement 13 recursiveCheckpointTarget (.ifS recursiveBranchCondition recursiveBranchBlock (some recursiveOuterElse) 0))
      recursiveBeforeBranch :=
    .call statements (.statementsHead 13 recursiveCheckpointTarget _ [] recursiveBeforeBranch)
  exact recursive_branch_reaches_return branch

theorem recursive_outer_trace_checked_handler {rootFuel : Nat}
    (reached : ExitReached rootFuel recursiveCheckpointConfig
      (.activation 16 recursiveOuterActivation [(0, .int .i64 0)] recursiveOuterBody 0) recursiveOuterEntered) :
    ExitReached rootFuel recursiveCheckpointConfig
      (.statement 4 recursiveCheckpointSource (.returnFrom 0 [.bytes array [66] 0] 0)) recursiveDirectCheckpoint ∧
    AcceptedWorld recursiveCheckpointConfig 0 recursiveDirectCheckpoint recursiveCheckpointAmbient
      recursiveCheckpointTypes recursiveCheckpointLive [] [] ∧
    EvaluationHistoryCoverage recursiveDirectCheckpoint recursiveCheckpointAmbient [] ∧
    ∃ after final : ExecutionState, enterActivation 16 recursiveCheckpointConfig recursiveOuterActivation [(0, .int .i64 0)] recursiveOuterBody 0 recursiveOuterEntered =
      .ok [.completed 1] final ∧ final.construction.stdout = after.construction.stdout := by
  obtain ⟨after, final, executed, stdout, _⟩ := recursive_checkpoint_outer_handler
  exact ⟨recursive_outer_activation_reaches_return reached, recursive_checkpoint_world,
    recursive_checkpoint_ambient_history, after, final, executed, stdout⟩

#print axioms recursive_outer_trace_checked_handler

#print axioms recursive_outer_activation_reaches_return

#print axioms recursive_branch_reaches_return

#print axioms recursive_helper_call_reaches_return

end Goose.Proofs.ConstructionAcceptedExecution
