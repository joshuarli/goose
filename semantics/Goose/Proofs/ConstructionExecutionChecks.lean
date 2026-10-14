import Goose.Proofs.ConstructionExecution

namespace Goose.Proofs.ConstructionExecutionChecks
open Goose.Construct

def accepts (module : Module) : Bool :=
  match validate module with | .ok _ => true | .error _ => false

def rawBytes : Module :=
  ⟨#["execution.goose"], #[], #[],
    #[⟨"entry", #[], #[], #[⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩],
      .mk 0 [.letS 0 (.bytes (.varr (.int .u8)) [65, 0, 255] 0) 0,
        .print [.view (.of (.var 0))] 0] none, .unknown⟩],
    #[⟨0, "entry", [], [], []⟩], 0, #[⟨0, 17, "let"⟩], #[], #[]⟩

def returnedObservation : ExecutionResult → Option (List UInt8 × List Goose.Core.ConstructionEvent)
  | .done .returned stdout events => some (stdout.data.toList, events)
  | _ => none

theorem rawBytes_validated : accepts rawBytes = true := by decide +kernel

theorem rawBytes_execution :
    returnedObservation (eval 100 .release rawBytes) =
      some ([65, 0, 255, 10], [.begin 0, .write 0 0, .write 0 1, .write 0 2, .publish 0]) := by
  decide +kernel

def terminalPrefix : Module := { rawBytes with
  impls := #[{ (rawBytes.impls[0]) with body := (.mk 0
    [.print [.text "before"] 0,
      .letS 0 (.bytes (.varr (.int .u8)) [65] 0) 0,
      .abort "stop" 0,
      .print [.text "after"] 0] none) }] }

def abortedObservation : ExecutionResult → Option (List UInt8 × List Goose.Core.ConstructionEvent)
  | .done (.aborted .userAbort 0) stdout events => some (stdout.data.toList, events)
  | _ => none

theorem terminalPrefix_validated : accepts terminalPrefix = true := by decide +kernel

theorem terminalPrefix_execution :
    abortedObservation (eval 100 .release terminalPrefix) =
      some ([98, 101, 102, 111, 114, 101, 10], [.begin 0, .write 0 0, .publish 0]) := by
  decide +kernel

def terminalProgram (message : String) (remaining : List Stmt) : Module :=
  ⟨#["terminal-execution.goose"], #[], #[],
    #[⟨"entry", #[], #[], #[], .mk 0 (.abort message 0 :: remaining) none, .unknown⟩],
    #[⟨0, "entry", [], [], []⟩], 0, #[⟨0, 17, "abort"⟩], #[], #[]⟩

theorem terminalProgram_execution (message : String) (remaining : List Stmt) :
    eval 100 .release (terminalProgram message remaining) =
      .done (.aborted .userAbort 0) ByteArray.empty [] := by
  cbv

#print axioms rawBytes_validated
#print axioms rawBytes_execution
#print axioms terminalPrefix_validated
#print axioms terminalPrefix_execution
#print axioms terminalProgram_execution

end Goose.Proofs.ConstructionExecutionChecks
