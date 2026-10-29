import Goose.Proofs.ConstructionExitInterruptedWriteTrace

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 4000000

namespace Goose.Proofs.ConstructionAcceptedExecution.InterruptedTrace
open Goose.Construct Goose.Core
open Goose.Proofs.ExitExecution

def interruptElementJumped : ExecutionState := Goose.Proofs.Exit.stepState
  (buildElement 7 interruptConfig interruptLoopScope 1 (.int .u8) interruptBranch interruptWritten)

def interruptProtected : ExecutionState := Goose.Proofs.Exit.stepState
  (buildExpr 8 interruptConfig interruptLoopScope 1 interruptOperand interruptPrepared)

def interruptExitJumped : ExecutionState := Goose.Proofs.Exit.stepState
  (withExitChannels interruptLoopScope recursiveCheckpointTarget [interruptOperand] 0
    (fun channels => evalOperands 10 interruptConfig interruptLoopScope channels [interruptOperand]) interruptLoopBound)

theorem interrupt_element_jump :
    buildElement 7 interruptConfig interruptLoopScope 1 (.int .u8) interruptBranch interruptWritten =
      .jump 6 (.breakValue []) interruptElementJumped := by cbv

theorem interrupt_destination_cleanup :
    cleanupReceivingDestination 0 1 [] interruptElementJumped = .ok () interruptProtected ∧
    buildExpr 8 interruptConfig interruptLoopScope 1 interruptOperand interruptPrepared =
      .jump 6 (.breakValue []) interruptProtected := by cbv

theorem interrupt_exit_cleanup :
    exitChannelCleanupBorrowed 0 [] [0] true [] interruptProtected = .ok () interruptExitJumped ∧
    withExitChannels interruptLoopScope recursiveCheckpointTarget [interruptOperand] 0
      (fun channels => evalOperands 10 interruptConfig interruptLoopScope channels [interruptOperand]) interruptLoopBound =
        .jump 6 (.breakValue []) interruptExitJumped ∧
    execStmt 11 interruptConfig interruptLoopScope (.returnFrom 0 [interruptOperand] 0) interruptLoopBound =
      .jump 6 (.breakValue []) interruptExitJumped := by
  constructor
  · cbv
  · constructor
    · cbv
    · cbv

theorem interrupt_cleanup_result :
    interruptExitJumped.construction.events = [.begin 0, .begin 1, .write 1 0, .abandon 1] ∧
    interruptExitJumped.construction.destinations[1]?.map PendingDestination.progress = some .abandoned ∧
    interruptExitJumped.construction.exitReservations[0]? = some .released ∧
    interruptExitJumped.construction.destinationResumptions.map Prod.fst = [1] := by cbv

theorem interrupt_reached_cleanup :
    ExitReached 44 interruptConfig (.statement 11 interruptLoopScope (.returnFrom 0 [interruptOperand] 0)) interruptLoopBound ∧
    ExitReached 44 interruptConfig (.element 7 interruptLoopScope 1 (.int .u8) interruptBranch) interruptWritten ∧
    execStmt 11 interruptConfig interruptLoopScope (.returnFrom 0 [interruptOperand] 0) interruptLoopBound =
      .jump 6 (.breakValue []) interruptExitJumped :=
  ⟨interrupt_return_reached, interrupt_second_element_reached, interrupt_exit_cleanup.2.2⟩

#print axioms interrupt_element_jump
#print axioms interrupt_destination_cleanup
#print axioms interrupt_exit_cleanup
#print axioms interrupt_cleanup_result
#print axioms interrupt_reached_cleanup

end Goose.Proofs.ConstructionAcceptedExecution.InterruptedTrace
