import Goose.Proofs.ExitExecutionChecks
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
open Goose.Construct Goose.Proofs.ExitExecutionChecks

namespace Goose.Proofs.ConstructionAcceptedExecution

def interruptedReturnBuilderBody : Goose.Construct.Block := .mk 0 [
  .ifS (.cmp .eq (.read (.var 0)) (.lit .i64 0))
    (.mk 1 [.expr (.call 2 [] 0) 0] none)
    (some (.mk 2 [.letS 1 (.call 1 [.byVal (.bin .sub (.read (.var 0)) (.lit .i64 1) 0)] 0) 0,
      .print [.view (.of (.var 1))] 0, .retValues [.bytes array [65] 0] 0] none)) 0,
  .retValues [.bytes array [68] 0] 0] none

def interruptedByteReturn : Module := { recursiveDestinations with impls := recursiveDestinations.impls.mapIdx fun i impl =>
  if i == 2 then { impl with body := .mk 0 [
    .while (.bool true) (.mk 1 [.returnFrom 0 [.arrLit array [.lit .u8 1,
      .ifE (.bool true) (.mk 2 [.brk 0] none) (.mk 3 [] (some (.lit .u8 2))) 0] 0] 0] none) 0,
    .returnFrom 0 [.bytes array [66] 0] 0] none } else if i == 1 then { impl with body := interruptedReturnBuilderBody } else impl }
theorem interrupted_byte_return_validated : validate interruptedByteReturn = .ok () := by cbv

theorem interrupted_byte_return_execution :
    returnedObservation (eval 200 .release interruptedByteReturn) =
      some ([66, 10, 65, 10], [.begin 0, .begin 1, .write 1 0, .abandon 1, .begin 2,
        .write 2 0, .publish 2, .write 0 0, .publish 0]) := by cbv

theorem interrupted_byte_return_cleanup :
    let state := Goose.Proofs.Exit.stepState (runModule 200 ⟨.release, interruptedByteReturn⟩ .initial)
    (state.construction.destinations.toList.map (·.progress), state.construction.exitReservations.toList,
      state.construction.destinationResumptions.map (·.1)) =
      ([.published 1, .abandoned, .published 1], [.released, .released, .released], [1]) := by cbv

#print axioms interrupted_byte_return_cleanup
#print axioms interrupted_byte_return_validated
#print axioms interrupted_byte_return_execution

end Goose.Proofs.ConstructionAcceptedExecution
