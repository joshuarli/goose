import Goose.Proofs.ConstructionAcceptedMixedRegisterModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem execStmt_print_integer (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (expression : Expr) (origin : Goose.Core.OriginId) (state : ExecutionState)
    (intTy : Goose.Core.IntTy) (number : Int)
    (evaluated : evalValue (fuel + 1) config environment expression state = .ok (.int intTy number) state) :
    execStmt (fuel + 3) config environment (.print [.expr expression] origin) state =
      .ok (.normal .unit) { state with construction :=
        { state.construction with stdout := state.construction.stdout ++ ((toString number).toUTF8 ++ "\n".toUTF8) } } := by
  simp [execStmt, evalPrintArg, evaluated, renderAny, renderValue, emitStdout, liftConstruction,
    appendStdout, ConstructionM.get, ConstructionM.set, bind, pure]

theorem execStmt_print_boolean (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (expression : Expr) (origin : Goose.Core.OriginId) (state : ExecutionState) (value : Bool)
    (evaluated : evalValue (fuel + 1) config environment expression state = .ok (.bool value) state) :
    execStmt (fuel + 3) config environment (.print [.expr expression] origin) state =
      .ok (.normal .unit) { state with construction :=
        { state.construction with stdout := state.construction.stdout ++
          ((if value then "true".toUTF8 else "false".toUTF8) ++ "\n".toUTF8) } } := by
  cases value <;> simp [execStmt, evalPrintArg, evaluated, renderAny, renderValue, emitStdout, liftConstruction,
    appendStdout, ConstructionM.get, ConstructionM.set, bind, pure]

theorem execStmt_print_expression_stopped (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (expression : Expr) (origin : Goose.Core.OriginId) (state after : ExecutionState) (stop : Goose.Core.Stop)
    (evaluated : evalValue fuel config environment expression state = .stop stop after) :
    execStmt (fuel + 2) config environment (.print [.expr expression] origin) state = .stop stop after := by
  simp [execStmt, evalPrintArg, evaluated, bind]

#print axioms execStmt_print_expression_stopped
#print axioms execStmt_print_integer
#print axioms execStmt_print_boolean
end Goose.Proofs.ConstructionAcceptedExecution
