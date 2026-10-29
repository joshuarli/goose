import Goose.Proofs.ConstructionExitInterruptedHelperTrace

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 4000000

namespace Goose.Proofs.ConstructionAcceptedExecution.InterruptedTrace
open Goose.Construct Goose.Core
open Goose.Proofs.ExitExecution
open Goose.Proofs.ExitExecutionChecks
open Goose.Proofs.ConstructionAcceptedExecution

def interruptLoopEntered : ExecutionState := { recursiveDirectCheckpoint with
  nextScope := recursiveDirectCheckpoint.nextScope + 1
  breaks := ⟨recursiveDirectCheckpoint.nextScope, recursiveCheckpointSource.act, .loop, []⟩ :: recursiveDirectCheckpoint.breaks }

def interruptLoopBound : ExecutionState := { interruptLoopEntered with nextScope := interruptLoopEntered.nextScope + 1 }

def interruptLoopScope : RuntimeActivation := { recursiveCheckpointSource with
  scopes := (1, interruptLoopEntered.nextScope) :: recursiveCheckpointSource.scopes }

def interruptBranch : Goose.Construct.Expr := .ifE (.bool true) (.mk 2 [.brk 0] none) (.mk 3 [] (some (.lit .u8 2))) 0

theorem interrupt_return_reached :
    ExitReached 44 interruptConfig (.statement 11 interruptLoopScope (.returnFrom 0 [interruptOperand] 0)) interruptLoopBound := by
  have loop : ExitReached 44 interruptConfig (.whileLoop 15 recursiveCheckpointSource (.bool true) interruptLoopBody) recursiveDirectCheckpoint :=
    .call interrupt_helper_loop_reached (.statements (.while 15 recursiveCheckpointSource (.bool true) interruptLoopBody 0 recursiveDirectCheckpoint))
  have condition : ((do expectBool (← evalValue 14 interruptConfig recursiveCheckpointSource (.bool true))) : EvalM Bool)
      recursiveDirectCheckpoint = .ok true recursiveDirectCheckpoint := by cbv
  have body : ExitReached 44 interruptConfig (.loop 14 recursiveCheckpointSource [] interruptLoopBody) recursiveDirectCheckpoint :=
    .call loop (.statements (.whileBody 14 recursiveCheckpointSource (.bool true) interruptLoopBody recursiveDirectCheckpoint recursiveDirectCheckpoint condition))
  have block : ExitReached 44 interruptConfig (.block 13 recursiveCheckpointSource [] [] interruptLoopBody) interruptLoopEntered := by
    exact .call body (.statements (by simpa [interruptLoopEntered] using
      StatementInvocationEdge.loopBlock (config := interruptConfig) 13 recursiveCheckpointSource [] interruptLoopBody recursiveDirectCheckpoint))
  have binding : bindAll recursiveCheckpointSource.act interruptLoopEntered.nextScope []
      { interruptLoopEntered with nextScope := interruptLoopEntered.nextScope + 1 } = .ok () interruptLoopBound := by cbv
  have statements : ExitReached 44 interruptConfig (.statements 12 interruptLoopScope [.returnFrom 0 [interruptOperand] 0]) interruptLoopBound := by
    have edge := ExitCallSite.blockStatements (config := interruptConfig) 12 recursiveCheckpointSource [] [] 1
      [.returnFrom 0 [interruptOperand] 0] none interruptLoopEntered interruptLoopBound binding
    exact .call block (by simpa [interruptLoopBody, interruptLoopScope] using edge)
  exact .call statements (.statementsHead 11 interruptLoopScope _ [] interruptLoopBound)

def interruptPrepared : ExecutionState := Goose.Proofs.Exit.stepState
  (exitChannels interruptLoopScope recursiveCheckpointTarget [interruptOperand] 0 interruptLoopBound)

theorem interrupt_operands_reached :
    ExitReached 44 interruptConfig (.operands 10 interruptLoopScope [.construct 1] [interruptOperand]) interruptPrepared := by
  have selected : targetActivation interruptConfig 0 interruptLoopBound = .ok recursiveCheckpointTarget interruptLoopBound := by cbv
  have setup : exitChannels interruptLoopScope recursiveCheckpointTarget [interruptOperand] 0 interruptLoopBound =
      .ok [.construct 1] interruptPrepared := by cbv
  exact .call interrupt_return_reached (.returnFromOperands 10 interruptLoopScope recursiveCheckpointTarget 0 [interruptOperand] 0
    interruptLoopBound interruptPrepared [.construct 1] selected setup)

def interruptWritten : ExecutionState := Goose.Proofs.Exit.stepState
  (buildElement 7 interruptConfig interruptLoopScope 1 (.int .u8) (.lit .u8 1) interruptPrepared)

theorem interrupt_second_element_reached :
    ExitReached 44 interruptConfig (.element 7 interruptLoopScope 1 (.int .u8) interruptBranch) interruptWritten := by
  have producer : ExitReached 44 interruptConfig (.produce 9 interruptLoopScope [.construct 1] interruptOperand) interruptPrepared :=
    .call interrupt_operands_reached (.operandsHead 9 interruptLoopScope (.construct 1) [] interruptOperand [] interruptPrepared)
  have receiving : ProducerReceivingPrefix interruptLoopScope [.construct 1] interruptOperand interruptPrepared [.construct 1] [.construct 1] interruptPrepared := by
    apply ProducerReceivingPrefix.actual interruptPrepared interruptPrepared interruptPrepared [.construct 1] [.construct 1] <;> cbv
  have builder : ExitReached 44 interruptConfig (.build 8 interruptLoopScope 1 interruptOperand) interruptPrepared := by
    apply ExitReached.call producer (.producer (.produce receiving ?_))
    apply ProducerBodyChild.build 1 interruptOperand interruptPrepared <;> simp [interruptOperand, producerSingleExpression]
  have renewed : liftConstruction 0 (renewReceivingDestination 1) interruptPrepared = .ok 1 interruptPrepared := by cbv
  have pending : getDestination 1 interruptPrepared = .ok recursiveCheckpointRow interruptPrepared := by cbv
  have element : Goose.Construct.elementType recursiveCheckpointRow.capability.logicalType = some (.int .u8) := by cbv
  have preceding : ((do for previous in [.lit .u8 1] do
      buildElement 7 interruptConfig interruptLoopScope 1 (.int .u8) previous) : EvalM Unit) interruptPrepared = .ok () interruptWritten := by cbv
  have site : BuilderBodyChild 7 interruptConfig interruptLoopScope 1 interruptOperand interruptPrepared
      (.element 7 interruptLoopScope 1 (.int .u8) interruptBranch) interruptWritten := by
    simpa [interruptOperand, interruptBranch] using BuilderBodyChild.array (fuel := 7) (config := interruptConfig) (environment := interruptLoopScope) (destination := 1) array
      [.lit .u8 1] [] interruptBranch 0 interruptPrepared interruptWritten recursiveCheckpointRow (.int .u8) pending element preceding
  exact .call builder (.producer (.build renewed site))

theorem interrupt_written_fresh_ticket :
    interruptWritten.construction.destinations[1]?.map PendingDestination.progress = some (.open 1) ∧
    interruptWritten.construction.events = [.begin 0, .begin 1, .write 1 0] ∧
    interruptWritten.construction.exitReservations[0]? = some (.active .fresh 1 1 recursiveCheckpointRow) := by cbv

#print axioms interrupt_written_fresh_ticket
#print axioms interrupt_return_reached
#print axioms interrupt_operands_reached
#print axioms interrupt_second_element_reached

end Goose.Proofs.ConstructionAcceptedExecution.InterruptedTrace
