import Goose.Proofs.ConstructionExitCheckpointCall

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ExitExecution
open Goose.Proofs.ExitExecutionChecks

def recursiveBeforeBranch : ExecutionState :=
  Goose.Proofs.Exit.stepState (runModule 22 recursiveCheckpointConfig .initial)

def recursiveBranchCondition : Expr :=
  .cmp .eq (.read (.var 0)) (.lit .i64 0)

def recursiveBranchBlock : Block := .mk 1 [.expr (.call 2 [] 0) 0] none

theorem recursive_checkpoint_branch_escape (otherwise : Option Block) :
    ∃ after : ExecutionState,
      let cleaned := { after with construction := { after.construction with
        exitReservations := after.construction.exitReservations.set! 0 .released } }
      let innerUnwound := releaseScopeState recursiveHelperActivation 0 recursiveHelperEntered.nextScope cleaned
      let crossed := { innerUnwound with activations := innerUnwound.activations.filter (fun current => current.act != recursiveHelperActivation.act) }
      let branchUnwound := releaseScopeState recursiveCheckpointTarget 1 recursiveBeforeBranch.nextScope crossed
      execStmt 13 recursiveCheckpointConfig recursiveCheckpointTarget
        (.ifS recursiveBranchCondition recursiveBranchBlock otherwise 0) recursiveBeforeBranch =
        .escape ⟨2, .nonlocal 0⟩ [.completed 1] branchUnwound ∧
      LandedResultChannels cleaned [.construct 1] [.varr (.int .u8)] [.completed 1] ∧
      RecursiveCheckpointOutsideFrame after := by
  obtain ⟨after, call, landed, outsideFrame⟩ := recursive_checkpoint_helper_call_escape
  let cleaned := { after with construction := { after.construction with
    exitReservations := after.construction.exitReservations.set! 0 .released } }
  let innerUnwound := releaseScopeState recursiveHelperActivation 0 recursiveHelperEntered.nextScope cleaned
  let crossed := { innerUnwound with activations := innerUnwound.activations.filter (fun current => current.act != recursiveHelperActivation.act) }
  have lookup : getImplementation recursiveCheckpointConfig 2 recursiveBeforeHelper = .ok (2, recursiveHelper) recursiveBeforeHelper := by cbv
  have channels : channelsFor recursiveCheckpointConfig.layout recursiveCallerScope.act recursiveHelper.results.toList 0 recursiveBeforeHelper =
      .ok [] recursiveBeforeHelper := by cbv
  have statement : execStmt 10 recursiveCheckpointConfig recursiveCallerScope (.expr (.call 2 [] 0) 0) recursiveBeforeHelper =
      .escape ⟨2, .nonlocal 0⟩ [.completed 1] crossed := by
    simp only [execStmt, evalValue, bind, lookup, channels, call]
    rfl
  have statements : execStmts 11 recursiveCheckpointConfig recursiveCallerScope [.expr (.call 2 [] 0) 0] recursiveBeforeHelper =
      .escape ⟨2, .nonlocal 0⟩ [.completed 1] crossed := by
    simp only [execStmts, bind, statement]
  have binding : bindAll recursiveCheckpointTarget.act recursiveBeforeBranch.nextScope []
      { recursiveBeforeBranch with nextScope := recursiveBeforeBranch.nextScope + 1 } = .ok () recursiveBeforeHelper := by cbv
  have localEnv : { recursiveCheckpointTarget with scopes := (1, recursiveBeforeBranch.nextScope) :: recursiveCheckpointTarget.scopes } =
      recursiveCallerScope := by cbv
  have block : execBlock 12 recursiveCheckpointConfig recursiveCheckpointTarget [] [] recursiveBranchBlock recursiveBeforeBranch =
      .escape ⟨2, .nonlocal 0⟩ [.completed 1]
        (releaseScopeState recursiveCheckpointTarget 1 recursiveBeforeBranch.nextScope crossed) := by
    simp only [recursiveBranchBlock, execBlock]
    have fresh : freshScope = fun state => .ok state.nextScope { state with nextScope := state.nextScope + 1 } := by
      funext state
      rfl
    rw [fresh]
    simp only [bind, withScope, binding, localEnv, statements, releaseScope, EvalM.get, EvalM.set]
  have condition : evalValue 12 recursiveCheckpointConfig recursiveCheckpointTarget recursiveBranchCondition recursiveBeforeBranch =
      .ok (.bool true) recursiveBeforeBranch := by cbv
  refine ⟨after, ?_, landed, outsideFrame⟩
  cases otherwise <;> simp only [execStmt, condition, bind, expectBool, pure, ↓reduceIte, block] <;> rfl

#print axioms recursive_checkpoint_branch_escape

end Goose.Proofs.ConstructionAcceptedExecution
