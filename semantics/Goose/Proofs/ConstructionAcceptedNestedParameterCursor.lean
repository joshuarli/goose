import Goose.Proofs.ConstructionAcceptedNestedParameterSource
import Goose.Proofs.ConstructionAcceptedUnaryArgumentSource

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem rpArgs_singleByValue_nextVar {env : PEnv} {expression : Expr} {before middle after : RState}
    {roots : List RootRef} {argumentRoots : List (List RootRef)}
    (operand : rpExpr env expression before = .ok (roots, middle))
    (checked : rpArgs env [.byVal expression] before = .ok (argumentRoots, after)) : after.nextVar = middle.nextVar := by
  exact (rpArgs_singleByValue_state operand checked).2

theorem rpExpr_singleByValue_nextVar {env : PEnv} {target : Goose.Core.ContextId} {context : Context} {callee : Impl}
    {parameter : Param} {expression : Expr} {before middle after : RState} {roots : List RootRef}
    {argumentRoots : List (List RootRef)} {origin : Nat}
    (contextAt : env.mod.contexts[target]? = some context) (calleeAt : env.mod.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter])
    (arguments : rpArgs env [.byVal expression] before = .ok (argumentRoots, middle))
    (checked : rpExpr env (.call target [.byVal expression] origin) before = .ok (roots, after)) :
    after.nextVar = middle.nextVar := by
  unfold rpExpr at checked
  simp only [arguments, bind, StateT.bind, Except.bind, contextAt, calleeAt, parameters,
    List.zip, List.zipWith, List.forIn_cons, List.forIn_nil, pure, StateT.pure, Except.pure] at checked
  cases content : checkContents env target [.byVal expression] argumentRoots with
  | error failure => simp [content, liftV] at checked
  | ok result =>
    cases result
    simp only [content, liftV] at checked
    split at checked
    · simp only [bind, StateT.bind] at checked
      cases updated : noteResultConstruction env middle with
      | error failure => simp [updated, Except.bind] at checked
      | ok pair =>
        have call : rpCall env target argumentRoots pair.2 = .ok (roots, after) := by
          simpa [updated, Except.bind] using checked
        have same : pair.2.nextVar = middle.nextVar := by
          simp [noteResultConstruction, modify] at updated
          cases updated
          rfl
        exact (rpCall_nextVar call).trans same
    · exact rpCall_nextVar checked

theorem typeExpr_singleByValueRegisterCall_after (fuel : Nat) (environment : TypingEnv) (contextId origin : Nat)
    (context : Context) (callee : Impl) (parameter : Param) (expression : Expr) (ty : Ty) (before middle after : Nat)
    (types : List Ty) (contextAt : environment.module.contexts[contextId]? = some context)
    (calleeAt : environment.module.impls[context.impl]? = some callee) (parameters : callee.params = #[parameter])
    (results : callee.results = #[⟨ty, .register, none⟩])
    (scalar : (∃ integer, ty = .int integer) ∨ ty = .bool)
    (requests : environment.resultRequests = [] ∨ environment.resultRequests = [.register])
    (arguments : typeArguments (fuel + 1) environment callee [parameter] [.byVal expression] before = .ok ((), middle))
    (checked : typeExpr (fuel + 2) environment (.call contextId [.byVal expression] origin) before = .ok (types, after)) :
    after = middle := by
  rcases requests with requests | requests <;> rcases scalar with ⟨integer, rfl⟩ | rfl <;>
    simp [typeExpr, contextAt, calleeAt, parameters, arguments, results, requests, Ty.nonfixed,
      bind, StateT.bind, pure, StateT.pure, Except.pure] at checked <;> cases checked <;> rfl

#print axioms typeExpr_singleByValueRegisterCall_after
#print axioms rpExpr_singleByValue_nextVar
#print axioms rpArgs_singleByValue_nextVar
end Goose.Proofs.ConstructionAcceptedExecution
