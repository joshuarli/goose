import Goose.Construct.Eval

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem evalArguments_twoByValue (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (variables : Array LocalVar) (first second : Param) (left right : Expr) (state : ExecutionState) :
    evalArguments (fuel + 2) config environment variables [first, second] [.byVal left, .byVal right] state =
      (do let firstValue ← evalValue (fuel + 1) config environment left
          let secondValue ← evalValue fuel config environment right
          let rest ← evalArguments fuel config environment variables [] []
          pure (firstValue :: secondValue :: rest)) state := by
  cases firstStep : evalValue (fuel + 1) config environment left state with
  | stop reason after | escape reason carriers after | jump target kind after =>
    simp [evalArguments, bind, pure, firstStep]
  | ok firstValue after =>
    cases secondStep : evalValue fuel config environment right after with
    | stop reason final | escape reason carriers final | jump target kind final =>
      simp [evalArguments, bind, pure, firstStep, secondStep]
    | ok secondValue final =>
      cases fuel <;> simp [evalArguments, bind, pure, firstStep, secondStep, timeout, EvalM.stop]

#print axioms evalArguments_twoByValue
end Goose.Proofs.ConstructionAcceptedExecution
