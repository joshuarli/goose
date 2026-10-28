import Goose.Proofs.ConstructionGhostRegisterProducer

namespace Goose.Proofs.ConstructionGhostScalarProducer
open Goose.Construct Goose.Proofs.ConstructionGhostProducerChannel Goose.Proofs.ConstructionGhostRegisterProducer

inductive ScalarExpression : Expr → Prop
  | integer (ty : Goose.Core.IntTy) (value : Int) : ScalarExpression (.lit ty value)
  | boolean (value : Bool) : ScalarExpression (.bool value)
  | unary (operation : Goose.Core.UnOp) (operand : Expr) (origin : Goose.Core.OriginId) : ScalarExpression (.un operation operand origin)
  | conversion (kind : Goose.Core.ConvKind) (target : Ty) (operand : Expr) (origin : Goose.Core.OriginId) :
      ScalarExpression (.conv kind target operand origin)
  | negation (operand : Expr) : ScalarExpression (.not operand)
  | comparison (operation : Goose.Core.CmpOp) (first second : Expr) : ScalarExpression (.cmp operation first second)
  | binary (operation : Goose.Core.BinOp) (first second : Expr) (origin : Goose.Core.OriginId) :
      ScalarExpression (.bin operation first second origin)
  | conjunction (first second : Expr) : ScalarExpression (.and first second)
  | disjunction (first second : Expr) : ScalarExpression (.or first second)

theorem scalarProducer_source (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (expression : Expr) (before : ExecutionState) (scalar : ScalarExpression expression) :
    evalProduce (fuel + 1) config environment channels expression before =
      (prepareProducerCallChannels environment expression channels >>= supportedProducerResult fuel config environment expression) before := by
  cases scalar <;> simp only [evalProduce, prepareProducerCallChannels, supportedProducerResult,
    Goose.Proofs.ConstructionGhostGlobalStep.evalM_bind_assoc] <;> rfl

inductive ValueProducerExpression : Expr → Prop
  | supported {expression : Expr} (supported : Goose.Proofs.ConstructionGhostSourceTransition.SupportedValue expression) :
      ValueProducerExpression expression
  | scalar {expression : Expr} (scalar : ScalarExpression expression) : ValueProducerExpression expression
  | bytes (ty : Ty) (bytes : List UInt8) (origin : Goose.Core.OriginId) : ValueProducerExpression (.bytes ty bytes origin)
  | array (ty : Ty) (operands : List Expr) (origin : Goose.Core.OriginId) : ValueProducerExpression (.arrLit ty operands origin)
  | fill (ty : Ty) (operand : Expr) (origin : Goose.Core.OriginId) : ValueProducerExpression (.fill ty operand origin)

theorem valueProducer_source (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (expression : Expr) (before : ExecutionState) (shape : ValueProducerExpression expression) :
    evalProduce (fuel + 1) config environment channels expression before =
      (prepareProducerCallChannels environment expression channels >>= supportedProducerResult fuel config environment expression) before := by
  cases shape with
  | supported supported => exact supportedProducer_source fuel config environment channels expression before supported
  | scalar scalar => exact scalarProducer_source fuel config environment channels expression before scalar
  | bytes | array | fill => simp only [evalProduce, prepareProducerCallChannels, supportedProducerResult,
      Goose.Proofs.ConstructionGhostGlobalStep.evalM_bind_assoc] <;> rfl

theorem scalarBuilder_source (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Goose.Core.DestinationId) (expression : Expr) (before : ExecutionState) (scalar : ScalarExpression expression) :
    buildExpr (fuel + 1) config environment incoming expression before =
      (do let destination ← liftConstruction (expressionOrigin expression) (renewReceivingDestination incoming)
          protectDestination (expressionOrigin expression) destination do
            let value ← evalValue fuel config environment expression
            copyValue fuel config.layout destination value (expressionOrigin expression) none) before := by
  cases scalar <;> simp only [buildExpr]

#print axioms valueProducer_source
#print axioms scalarProducer_source
#print axioms scalarBuilder_source
end Goose.Proofs.ConstructionGhostScalarProducer
