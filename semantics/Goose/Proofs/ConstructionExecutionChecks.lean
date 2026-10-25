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
  cbv

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
  cbv

def terminalProgram (message : String) (remaining : List Stmt) : Module :=
  ⟨#["terminal-execution.goose"], #[], #[],
    #[⟨"entry", #[], #[], #[], .mk 0 (.abort message 0 :: remaining) none, .unknown⟩],
    #[⟨0, "entry", [], [], []⟩], 0, #[⟨0, 17, "abort"⟩], #[], #[]⟩

theorem terminalProgram_execution (message : String) (remaining : List Stmt) :
    eval 100 .release (terminalProgram message remaining) =
      .done (.aborted .userAbort 0) ByteArray.empty [] := by
  cbv

def afterRawBytes : ExecutionState :=
  Goose.Proofs.Exit.stepState (runModule 100 ⟨.release, rawBytes⟩ .initial)

theorem reachable_terminal_keeps_earlier_events :
    Goose.Proofs.ConstructionExecution.EventPrefix afterRawBytes.construction.events
      (Goose.Proofs.Exit.stepState
        (runModule 100 ⟨.release, terminalPrefix⟩ afterRawBytes)).construction.events :=
  Goose.Proofs.ConstructionExecution.runModule_keepsEventPrefix _ _ _

def stoppedObservation : ExecutionStep Unit →
    Option (List UInt8 × List Goose.Core.ConstructionEvent)
  | .stop (.abort .userAbort 0) state => some (state.construction.stdout.data.toList,
      state.construction.events)
  | _ => none

theorem reachable_terminal_execution :
    stoppedObservation (runModule 100 ⟨.release, terminalPrefix⟩ afterRawBytes) =
      some ([65, 0, 255, 10, 98, 101, 102, 111, 114, 101, 10],
        [.begin 0, .write 0 0, .write 0 1, .write 0 2, .publish 0,
          .begin 1, .write 1 0, .publish 1]) := by
  cbv

theorem reachable_terminal_preserves_published_bytes :
    ((Goose.Proofs.Exit.stepState
      (runModule 100 ⟨.release, terminalPrefix⟩ afterRawBytes)).construction.storage[0]?).map
        (fun storage => storage.bytes.data.toList) = some [3, 0, 0, 0, 65, 0, 255] := by
  cbv

def effectfulFill (count : Nat) : Module :=
  let ty := Ty.arr (.varr (.int .u8)) count
  ⟨#["fill-execution.goose"], #[], #[],
    #[⟨"entry", #[], #[], #[⟨"result", ty, .immutable, 0, 0⟩],
      .mk 0 [.letS 0 (.fill ty
        (.blockE (.mk 1 [.print [.text "once"] 0]
          (some (.bytes (.varr (.int .u8)) [66] 0))) 0) 0) 0,
        .print ((List.range count).map fun index =>
          .view (.of (.elem (.of (.var 0)) (.lit .i64 (Int.ofNat index)) 0))) 0] none,
      .unknown⟩], #[⟨0, "entry", [], [], []⟩], 0, #[⟨0, 17, "let"⟩], #[], #[]⟩

theorem effectfulFill_validated : accepts (effectfulFill 2) = true := by cbv

theorem effectfulFill_execution :
    returnedObservation (eval 100 .release (effectfulFill 2)) =
      some ([111, 110, 99, 101, 10, 66, 66, 10],
        [.begin 0, .begin 1, .write 1 0, .copy (.repeat 1) 0, .write 0 0,
          .copy (.repeat 1) 0, .write 0 1, .publish 0]) := by cbv

theorem zeroFill_rejected : validate (effectfulFill 0) =
    .error ⟨.type, "invalid fixed-array element or count"⟩ := by cbv

def preparationEnvironment : RuntimeActivation := ⟨0, 0, #[], [], []⟩

def preparationOperands : List Expr :=
  [.blockE (.mk 0 [.print [.text "operand"] 0] (some (.lit .i64 7))) 0, .lit .i64 8]

def preparationChannels : List Channel := [.register (.int .i64), .construct 0]

def preparationObservation : ExecutionStep α → Option (List UInt8)
  | .stop (.fault .unbound) state => some state.construction.stdout.data.toList
  | _ => none

theorem values_preparation_failure_precedes_operands :
    preparationObservation
      (evalProduce 20 ⟨.release, rawBytes⟩ preparationEnvironment preparationChannels
        (.values preparationOperands) .initial) = some [] := by
  cbv

theorem operands_without_outer_preparation_run_first_operand :
    preparationObservation
      (evalOperands 19 ⟨.release, rawBytes⟩ preparationEnvironment preparationChannels
        preparationOperands .initial) = some [111, 112, 101, 114, 97, 110, 100, 10] := by
  cbv

#print axioms values_preparation_failure_precedes_operands
#print axioms operands_without_outer_preparation_run_first_operand
#print axioms rawBytes_validated
#print axioms rawBytes_execution
#print axioms terminalPrefix_validated
#print axioms terminalPrefix_execution
#print axioms terminalProgram_execution
#print axioms reachable_terminal_keeps_earlier_events
#print axioms reachable_terminal_execution
#print axioms reachable_terminal_preserves_published_bytes
#print axioms effectfulFill_validated
#print axioms effectfulFill_execution
#print axioms zeroFill_rejected
#print axioms Goose.Proofs.ConstructionExecution.evaluation_keepsEventPrefix
#print axioms Goose.Proofs.ConstructionExecution.runModule_keepsEventPrefix
#print axioms Goose.Proofs.ConstructionExecution.evaluation_preservesConstructionBegins
#print axioms Goose.Proofs.ConstructionExecution.runModule_preservesConstructionBegins
#print axioms Goose.Proofs.ConstructionExecution.runModule_destinationBeginIds
#print axioms Goose.Proofs.ConstructionExecution.runModule_distinctDestinationBegins
#print axioms Goose.Proofs.ConstructionExecution.runModule_destinationBegins_cover

end Goose.Proofs.ConstructionExecutionChecks
