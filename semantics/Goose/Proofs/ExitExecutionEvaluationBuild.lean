import Goose.Proofs.ExitExecutionEvaluationProduce

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

set_option maxHeartbeats 2000000 in
theorem buildExpr_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (expression : Expr) :
    PreservesFresh (buildExpr (fuel + 1) config environment destination expression) := by
  cases expression <;> try simp only [buildExpr]
  all_goals fresh_eval previous

#print axioms buildExpr_preservesFresh_succ

end Goose.Proofs.ExitExecution
