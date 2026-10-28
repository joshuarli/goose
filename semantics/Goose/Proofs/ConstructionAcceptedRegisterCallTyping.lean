import Goose.Proofs.ConstructionAcceptedRegisterInitializerPosition

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem typeExpr_registerCall_result (fuel : Nat) (environment : TypingEnv) (contextId origin : Nat)
    (context : Context) (callee : Impl) (arguments : List Arg) (resultTy : Ty) (before after : Nat) (types : List Ty)
    (contextAt : environment.module.contexts[contextId]? = some context)
    (calleeAt : environment.module.impls[context.impl]? = some callee)
    (results : callee.results = #[⟨resultTy, .register, none⟩])
    (scalar : (∃ intTy, resultTy = .int intTy) ∨ resultTy = .bool)
    (requests : environment.resultRequests = [])
    (checked : typeExpr (fuel + 1) environment (.call contextId arguments origin) before = .ok (types, after)) :
    types = [resultTy] := by
  rcases scalar with ⟨intTy, rfl⟩ | rfl <;>
    simp only [typeExpr, contextAt, calleeAt, bind, StateT.bind] at checked <;>
    cases args : typeArguments fuel environment callee callee.params.toList arguments before with
    | error failure => simp only [args, Except.bind, reduceCtorEq] at checked
    | ok result =>
      obtain ⟨unit, middle⟩ := result
      cases unit
      simp [args, results, requests, Ty.nonfixed, bind, StateT.bind, pure, StateT.pure, Except.pure] at checked
      simp only [Except.bind, StateT.pure, Except.pure] at checked
      cases checked
      rfl

#print axioms typeExpr_registerCall_result
end Goose.Proofs.ConstructionAcceptedExecution
