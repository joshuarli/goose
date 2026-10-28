import Goose.Construct.Typing

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem typeExpr_call_scalarOperand (fuel : Nat) (environment : TypingEnv) (contextId : Nat)
    (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar) (expression : Expr)
    (origin : Nat) (before after : Nat) (types : List Ty)
    (contextAt : environment.module.contexts[contextId]? = some context)
    (calleeAt : environment.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (mode : parameter.mode = .byValue)
    (declared : callee.vars[parameter.var]? = some descriptor)
    (checked : typeExpr (fuel + 2) environment (.call contextId [.byVal expression] origin) before = .ok (types, after)) :
    ∃ ty middle, typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] }
        expression before = .ok ([ty], middle) ∧ ty.passesTo descriptor.ty = true := by
  obtain ⟨middle, arguments⟩ := typeExpr_call_arguments (fuel + 1) environment contextId context callee
    [.byVal expression] origin before after types contextAt calleeAt checked
  have args : typeArguments (fuel + 1) environment callee [parameter] [.byVal expression] before = .ok ((), middle) := by
    simpa [parameters] using arguments
  exact typeArguments_scalar_operand fuel environment callee parameter descriptor expression before middle mode declared args

#print axioms typeArguments_scalar_operand
#print axioms typeExpr_call_arguments
#print axioms typeExpr_call_scalarOperand
end Goose.Proofs.ConstructionAcceptedExecution
