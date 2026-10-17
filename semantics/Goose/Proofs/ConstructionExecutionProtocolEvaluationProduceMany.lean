import Goose.Proofs.ConstructionExecutionProtocolEvaluationContext

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct

variable {predicate : ConstructionState → Prop} [primitives : ConstructionProtocolPrimitives predicate]
  [reservations : ConstructionReservationPrimitives predicate]
include primitives reservations

set_option maxHeartbeats 2000000 in
theorem evalProduce_many_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionInvariant (predicate := predicate) fuel config)
    (environment : RuntimeActivation) (first second : Channel) (rest : List Channel) (expression : Expr) :
    PreservesConstructionInvariant predicate (evalProduce (fuel + 1) config environment (first :: second :: rest) expression) := by
  cases expression <;> simp only [evalProduce]
  all_goals protocol_eval previous

end Goose.Proofs.ConstructionExecutionProtocol
