import Goose.Proofs.ExitExecutionChecks

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ExitExecutionChecks

def byteArgumentReceivingRenewal : Module :=
  let integer : Ty := .int .i64
  let byte : Ty := .int .u8
  let result : Ty := .varr byte
  let interrupted := Expr.arrLit result [.lit .u8 1,
    .ifE (.bool true) (.mk 4 [.brk 0] none) (.mk 5 [] (some (.lit .u8 2))) 0] 0
  let argument := Expr.ifE (.bool true)
    (.mk 2 [.while (.bool true) (.mk 3 [.breakValue interrupted 0] none) 0,
      .print [.text "argument finished"] 0] (some (.lit .i64 0)))
    (.mk 6 [] (some (.lit .i64 0))) 0
  let entry : Impl := ⟨"entry", #[], #[], #[⟨"result", result, .immutable, 0, 0⟩],
    .mk 0 [.letS 0 (.call 1 [] 0) 0, .print [.view (.of (.var 0))] 0] none, .unknown⟩
  let caller : Impl := ⟨"caller", #[], #[⟨result, .value, none⟩], #[],
    .mk 0 [] (some (.blockE (.mk 1 [] (some (.call 2 [.byVal argument] 0))) 0)), .unknown⟩
  let helper : Impl := ⟨"helper", #[⟨0, .byValue⟩], #[⟨result, .value, none⟩],
    #[⟨"parameter", integer, .immutable, 0, 0⟩],
    .mk 0 [.print [.text "helper entered"] 0] (some (.arrLit result [.lit .u8 9] 0)), .unknown⟩
  ⟨#["byte-argument-renewal.goose"], #[integer, byte, result], #[], #[entry, caller, helper],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "caller", [], [[]], []⟩, ⟨2, "helper", [], [[]], []⟩], 0,
    #[⟨0, 1, "call"⟩], #[], #[]⟩

theorem byte_argument_renewal_validated : validate byteArgumentReceivingRenewal = .ok () := by cbv

theorem byte_argument_renewal_execution :
    returnedObservation (eval 100 .release byteArgumentReceivingRenewal) =
      some ("argument finished\nhelper entered\n\t\n".toUTF8.data.toList,
        [.begin 0, .write 0 0, .abandon 0, .begin 1, .write 1 0, .publish 1]) := by decide +kernel

theorem byte_argument_renewal_destinations :
    let state := Goose.Proofs.Exit.stepState (runModule 100 ⟨.release, byteArgumentReceivingRenewal⟩ .initial)
    (state.construction.destinations[0]?.map PendingDestination.progress,
      state.construction.destinationResumptions.map Prod.fst,
      state.construction.destinations[1]?.map PendingDestination.progress) =
        (some .abandoned, [0], some (.published 1)) := by decide +kernel

#print axioms byte_argument_renewal_validated
#print axioms byte_argument_renewal_execution
#print axioms byte_argument_renewal_destinations

end Goose.Proofs.ConstructionAcceptedExecution
