import Goose.Proofs.ConstructionExecutionProtocolEvaluationContext

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct

variable {predicate : ConstructionState → Prop} [primitives : ConstructionProtocolPrimitives predicate]
  [reservations : ConstructionReservationPrimitives predicate]
include primitives reservations

set_option maxHeartbeats 2000000 in
theorem evalProduce_construct_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionInvariant (predicate := predicate) fuel config)
    (environment : RuntimeActivation) (destination : Goose.Core.DestinationId) (expression : Expr) :
    PreservesConstructionInvariant predicate (evalProduce (fuel + 1) config environment [.construct destination] expression) := by
  cases expression <;> simp only [evalProduce]
  all_goals protocol_eval previous

end Goose.Proofs.ConstructionExecutionProtocol
