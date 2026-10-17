import Goose.Construct.Eval

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct

inductive OwnershipResultShape : Type → Type 1
  | none {α : Type} : OwnershipResultShape α
  | carrier : OwnershipResultShape Construct.Carrier
  | carriers : OwnershipResultShape (List Construct.Carrier)
  | resultScope : OwnershipResultShape (Construct.Flow × List Construct.Carrier)

def OwnershipResultShape.retainedCarriers : OwnershipResultShape α → α → List Construct.Carrier
  | .none, _ => []
  | .carrier, value => [value]
  | .carriers, values => values
  | .resultScope, value => value.2

inductive OwnershipEvaluationAction (fuel : Nat) (config : EvalConfig) :
    {α : Type} → OwnershipResultShape α → EvalM α → Prop
  | value environment expression :
      OwnershipEvaluationAction fuel config .none (evalValue fuel config environment expression)
  | bound environment count defaultValue operand :
      OwnershipEvaluationAction fuel config .none (evalBound fuel config environment count defaultValue operand)
  | place environment operand :
      OwnershipEvaluationAction fuel config .none (evalPlace fuel config environment operand)
  | view environment operand :
      OwnershipEvaluationAction fuel config .none (evalView fuel config environment operand)
  | produce environment channels operand :
      OwnershipEvaluationAction fuel config .carriers (evalProduce fuel config environment channels operand)
  | operands environment channels expressions :
      OwnershipEvaluationAction fuel config .carriers (evalOperands fuel config environment channels expressions)
  | build environment destination expression :
      OwnershipEvaluationAction fuel config .none (buildExpr fuel config environment destination expression)
  | element environment destination element expression :
      OwnershipEvaluationAction fuel config .none (buildElement fuel config environment destination element expression)
  | arguments environment vars params args :
      OwnershipEvaluationAction fuel config .none (evalArguments fuel config environment vars params args)
  | call environment context args channels origin :
      OwnershipEvaluationAction fuel config .carriers (invokeCall fuel config environment context args channels origin)
  | activation environment pre body origin :
      OwnershipEvaluationAction fuel config .carriers (enterActivation fuel config environment pre body origin)
  | activationBody environment pre body :
      OwnershipEvaluationAction fuel config .carriers (execActivationBody fuel config environment pre body)
  | resultBlock environment channels body :
      OwnershipEvaluationAction fuel config .resultScope (execResultBlock fuel config environment channels body)
  | resultBlockWith environment pre channels body :
      OwnershipEvaluationAction fuel config .resultScope (execResultBlockWith fuel config environment pre channels body)
  | block environment pre channels body :
      OwnershipEvaluationAction fuel config .none (execBlock fuel config environment pre channels body)
  | statements environment statements :
      OwnershipEvaluationAction fuel config .none (execStmts fuel config environment statements)
  | statement environment statement :
      OwnershipEvaluationAction fuel config .none (execStmt fuel config environment statement)
  | printArgument environment argument :
      OwnershipEvaluationAction fuel config .none (evalPrintArg fuel config environment argument)
  | whileLoop environment condition body :
      OwnershipEvaluationAction fuel config .none (execWhile fuel config environment condition body)
  | rangeLoop environment var ty first last body :
      OwnershipEvaluationAction fuel config .none (execRange fuel config environment var ty first last body)
  | eachLoop environment var index byRef body view current :
      OwnershipEvaluationAction fuel config .none (execEach fuel config environment var index byRef body view current)
  | loop environment pre body :
      OwnershipEvaluationAction fuel config .none (loopBody fuel config environment pre body)
  | push environment owner expression origin :
      OwnershipEvaluationAction fuel config .none (pushValue fuel config environment owner expression origin)

end Goose.Proofs.ConstructionExecutionOwnership
