import Goose.Proofs.ConstructionAcceptedRegisterCallTyping

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem typeExpr_zeroArgumentRegisterCall_cursor (fuel : Nat) (environment : TypingEnv) (contextId origin : Nat)
    (context : Context) (callee : Impl) (resultTy : Ty) (before after : Nat) (types : List Ty)
    (contextAt : environment.module.contexts[contextId]? = some context)
    (calleeAt : environment.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[])
    (results : callee.results = #[⟨resultTy, .register, none⟩])
    (scalar : (∃ intTy, resultTy = .int intTy) ∨ resultTy = .bool)
    (requests : environment.resultRequests = [] ∨ environment.resultRequests = [.register])
    (checked : typeExpr (fuel + 2) environment (.call contextId [] origin) before = .ok (types, after)) :
    after = before := by
  rcases requests with requests | requests <;> rcases scalar with ⟨intTy, rfl⟩ | rfl <;>
    simp [typeExpr, contextAt, calleeAt, parameters, typeArguments, results, requests, Ty.nonfixed,
      bind, StateT.bind, pure, StateT.pure, Except.pure] at checked <;> cases checked <;> rfl

#print axioms typeExpr_zeroArgumentRegisterCall_cursor
end Goose.Proofs.ConstructionAcceptedExecution
