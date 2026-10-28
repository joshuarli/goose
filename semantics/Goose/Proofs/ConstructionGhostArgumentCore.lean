import Goose.Construct.Eval

namespace Goose.Proofs.ConstructionGhostArguments
open Goose.Construct

def argumentValue (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (parameterVars : Array LocalVar) (parameter : Param) (argument : Arg) : EvalM Value := do
  match argument with
  | .byRef _ place => pure (.ref (← evalPlace fuel config environment place))
  | .byVal operand => evalValue fuel config environment operand
  | .construct operand =>
      let some localVar := parameterVars[parameter.var]? | fault .unbound
      let materialized ← materializeProducer fuel ⟨config.module, environment.vars⟩ operand
        (evalValue fuel config environment operand)
      let carrier ← match materialized with
        | some values => do
            let destination ← materializedDestination fuel config.layout environment.act localVar.ty
              (expressionOrigin operand) values.size (.fixed values)
            publishCarriers (expressionOrigin operand) [.completed destination]
            pure (Carrier.completed destination)
        | none =>
            constructLocal ⟨config.module, environment.vars⟩ environment.act localVar.ty (expressionOrigin operand) operand
              (fun destination => buildExpr fuel config environment destination operand)
      carrierValue carrier

theorem evalArguments_step (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (parameterVars : Array LocalVar) (parameter : Param) (parameters : List Param)
    (argument : Arg) (arguments : List Arg) (before : ExecutionState) :
    evalArguments (fuel + 1) config environment parameterVars (parameter :: parameters) (argument :: arguments) before =
      (do let value ← argumentValue fuel config environment parameterVars parameter argument
          pure (value :: (← evalArguments fuel config environment parameterVars parameters arguments))) before := by
  cases argument <;> simp [evalArguments, argumentValue, bind, pure]
  all_goals cases found : parameterVars[parameter.var]? <;> try simp_all [bind, pure]
  all_goals repeat' (split <;> try simp_all [bind, pure])

#print axioms evalArguments_step
end Goose.Proofs.ConstructionGhostArguments
