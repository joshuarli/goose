import Goose.Proofs.ExitExecutionEvaluationValues

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

set_option maxHeartbeats 2000000 in
theorem evalProduce_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (expression : Expr) :
    PreservesFresh (evalProduce (fuel + 1) config environment channels expression) := by
  cases expression <;> simp only [evalProduce]
  all_goals fresh_eval previous


#print axioms evalProduce_preservesFresh_succ

end Goose.Proofs.ExitExecution
