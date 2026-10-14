import Goose.Proofs.ExitExecution
import Goose.Construct.Validate

namespace Goose.Proofs.ExitExecutionChecks
open Goose.Construct

def array : Ty := .varr (.int .u8)

def recursiveDestinations : Module :=
  ⟨#["exit-execution.goose"], #[], #[],
    #[⟨"entry", #[], #[], #[⟨"result", array, .immutable, 0, 0⟩],
      .mk 0 [.letS 0 (.call 1 [.byVal (.lit .i64 1)] 0) 0,
        .print [.view (.of (.var 0))] 0] none,
      .known ⟨[], [], [], [], [], [], [], [], true, true⟩⟩,
      ⟨"builder", #[⟨0, .byValue⟩], #[⟨array, .value, none⟩],
        #[⟨"depth", .int .i64, .immutable, 0, 0⟩, ⟨"inner", array, .immutable, 2, 0⟩],
        .mk 0 [.ifS (.cmp .eq (.read (.var 0)) (.lit .i64 0))
          (.mk 1 [.expr (.call 2 [] 0) 0] none)
          (some (.mk 2 [.letS 1 (.call 1 [.byVal (.bin .sub (.read (.var 0)) (.lit .i64 1) 0)] 0) 0,
            .print [.view (.of (.var 1))] 0, .retValues [.bytes array [65] 0] 0] none)) 0] none,
        .known ⟨[], [], [], [], [], [0], [], [], true, true⟩⟩,
      ⟨"helper", #[], #[], #[], .mk 0 [.returnFrom 0 [.bytes array [66] 0] 0] none,
        .known ⟨[], [], [], [], [], [], [0], [0], false, false⟩⟩],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "builder", [], [[]], []⟩,
      ⟨2, "helper", [], [], []⟩], 0, #[⟨0, 17, "call"⟩], #[], #[⟨1, []⟩]⟩

def accepts (module : Module) : Bool :=
  match validate module with | .ok _ => true | .error _ => false

def returnedObservation : ExecutionResult → Option (List UInt8 × List Goose.Core.ConstructionEvent)
  | .done .returned stdout events => some (stdout.data.toList, events)
  | _ => none

theorem recursiveDestinations_validated : accepts recursiveDestinations = true := by cbv

theorem recursiveDestinations_execution :
    returnedObservation (eval 200 .release recursiveDestinations) =
      some ([66, 10, 65, 10], [.begin 0, .begin 1, .write 1 0, .publish 1, .write 0 0, .publish 0]) := by
  decide +kernel

#print axioms recursiveDestinations_validated
#print axioms recursiveDestinations_execution
#print axioms Goose.Proofs.ExitExecution.preservesFresh_copyValue
#print axioms Goose.Proofs.ExitExecution.preservesFresh_deliverCarriers
#print axioms Goose.Proofs.ExitExecution.preservesFresh_truncateOwner
#print axioms Goose.Proofs.ExitExecution.preservesFresh_appendFixedValues
#print axioms Goose.Proofs.ExitExecution.preservesFresh_appendRun

end Goose.Proofs.ExitExecutionChecks
