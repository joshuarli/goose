import Goose.Proofs.ConstructionExecutionProtocolEvaluationProduceNil
import Goose.Proofs.ConstructionExecutionProtocolEvaluationProduceRegister
import Goose.Proofs.ConstructionExecutionProtocolEvaluationProduceConstruct
import Goose.Proofs.ConstructionExecutionProtocolEvaluationProduceMany

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct

variable {predicate : ConstructionState → Prop} [primitives : ConstructionProtocolPrimitives predicate]
  [reservations : ConstructionReservationPrimitives predicate]
include primitives reservations

set_option maxHeartbeats 2000000 in
theorem evalProduce_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (expression : Expr) :
    (PreservesConstructionInvariant predicate) (evalProduce (fuel + 1) config environment channels expression) := by
  cases channels with
  | nil => exact evalProduce_nil_preservesConstructionInvariant_succ fuel config previous environment expression
  | cons channel rest =>
      cases rest with
      | nil =>
          cases channel with
          | register ty => exact evalProduce_register_preservesConstructionInvariant_succ fuel config previous environment ty expression
          | completion token =>
              cases expression <;> simp only [evalProduce]
              all_goals protocol_eval previous
          | construct destination => exact evalProduce_construct_preservesConstructionInvariant_succ fuel config previous environment destination expression
      | cons second rest => exact evalProduce_many_preservesConstructionInvariant_succ fuel config previous environment channel second rest expression

end Goose.Proofs.ConstructionExecutionProtocol
