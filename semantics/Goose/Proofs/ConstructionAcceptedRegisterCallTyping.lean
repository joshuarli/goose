import Goose.Proofs.ConstructionAcceptedRegisterInitializerPosition
import Goose.Proofs.ConstructionAcceptedScalarLocalTyping
import Goose.Proofs.ConstructionAcceptedScalarLocalCursor

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem typeExpr_registerCall_result_general (fuel : Nat) (environment : TypingEnv) (contextId origin : Nat)
    (context : Context) (callee : Impl) (arguments : List Arg) (resultTy : Ty) (before after : Nat) (types : List Ty)
    (contextAt : environment.module.contexts[contextId]? = some context)
    (calleeAt : environment.module.impls[context.impl]? = some callee)
    (results : callee.results = #[⟨resultTy, .register, none⟩])
    (scalar : (∃ intTy, resultTy = .int intTy) ∨ resultTy = .bool)
    (requests : environment.resultRequests = [] ∨ environment.resultRequests = [.register])
    (checked : typeExpr (fuel + 1) environment (.call contextId arguments origin) before = .ok (types, after)) :
    types = [resultTy] := by
  rcases requests with requests | requests <;> rcases scalar with ⟨intTy, rfl⟩ | rfl <;>
    simp only [typeExpr, contextAt, calleeAt, bind, StateT.bind] at checked <;>
    cases args : typeArguments fuel environment callee callee.params.toList arguments before with
    | error failure => simp only [args, Except.bind, reduceCtorEq] at checked
    | ok result =>
      obtain ⟨token, middle⟩ := result
      cases token
      simp [args, results, requests, Ty.nonfixed, bind, StateT.bind, pure, StateT.pure, Except.pure] at checked
      simp only [Except.bind, StateT.pure] at checked
      cases checked
      rfl



theorem typeExpr_registerCall_result (fuel : Nat) (environment : TypingEnv) (contextId origin : Nat)
    (context : Context) (callee : Impl) (arguments : List Arg) (resultTy : Ty) (before after : Nat) (types : List Ty)
    (contextAt : environment.module.contexts[contextId]? = some context)
    (calleeAt : environment.module.impls[context.impl]? = some callee)
    (results : callee.results = #[⟨resultTy, .register, none⟩])
    (scalar : (∃ intTy, resultTy = .int intTy) ∨ resultTy = .bool)
    (requests : environment.resultRequests = [])
    (checked : typeExpr (fuel + 1) environment (.call contextId arguments origin) before = .ok (types, after)) :
    types = [resultTy] :=
  typeExpr_registerCall_result_general fuel environment contextId origin context callee arguments resultTy before after types
    contextAt calleeAt results scalar (Or.inl requests) checked

private theorem registerLocal_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl, checked⟩

theorem typeStatement_registerCall_result (fuel : Nat) (environment next : TypingEnv) (id contextId callOrigin origin : Nat)
    (arguments : List Arg) (before after : Nat) (context : Context) (callee : Impl) (resultTy : Ty)
    (contextAt : environment.module.contexts[contextId]? = some context)
    (calleeAt : environment.module.impls[context.impl]? = some callee)
    (results : callee.results = #[⟨resultTy, .register, none⟩])
    (resultScalar : (∃ intTy, resultTy = .int intTy) ∨ resultTy = .bool)
    (targetScalar : ∀ descriptor, environment.variables[id]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (typed : typeStatement (fuel + 1) environment (.letS id (.call contextId arguments callOrigin) origin) before = .ok (next, after)) :
    ∃ descriptor, environment.variables[id]? = some descriptor ∧ id = before ∧ descriptor.ty = resultTy := by
  obtain ⟨descriptor, declared, scope, order⟩ := typeStatement_let_descriptor fuel environment next id
    (.call contextId arguments callOrigin) origin before after typed
  have descriptorScalar := targetScalar descriptor declared
  subst id
  simp only [typeStatement, bind, StateT.bind] at typed
  change Except.bind (((do
    let expected ← get
    if before != expected then throw ⟨.type, "variables must be declared once in ascending order"⟩
    let some localVar := environment.variables[before]? | throw ⟨.type, "declared localVar outside table"⟩
    if localVar.scope != environment.scope || !localVar.ty.storable then throw ⟨.type, "localVar scope or type mismatch"⟩
    set (expected + 1)
    pure localVar) : TypingM LocalVar) before) _ = _ at typed
  have getState (state : Nat) : (get : TypingM Nat) state = .ok (state, state) := rfl
  have setState (next state : Nat) : (set next : TypingM Unit) state = .ok ((), next) := rfl
  simp only [bind, StateT.bind, getState, Except.bind, bne_self_eq_false, declared, scope,
    bne_self_eq_false, Bool.false_or] at typed
  cases storable : descriptor.ty.storable with
  | false =>
    simp only [storable, Bool.not_false, ↓reduceIte] at typed
    change Except.error _ = Except.ok _ at typed
    cases typed
  | true =>
    simp only [storable, Bool.not_true, pure, StateT.pure, Except.pure] at typed
    obtain ⟨result, expressionTyped, remaining⟩ := registerLocal_bind_success _ _ _ typed
    obtain ⟨types, counter⟩ := result
    cases fuel with
    | zero =>
      change Except.error _ = Except.ok _ at expressionTyped
      cases expressionTyped
    | succ fuel =>
      have resultTypes := typeExpr_registerCall_result fuel
        { environment with use := .ordinary, request := .value, resultRequests := [] }
        contextId callOrigin context callee arguments resultTy (before + 1) counter types
        contextAt calleeAt results resultScalar rfl expressionTyped
      subst types
      unfold_scalar_typing_helpers
      cases passing : resultTy.passesTo descriptor.ty with
      | false =>
        simp only [pure, StateT.pure, Except.pure, passing, Bool.false_eq_true, ↓reduceIte] at remaining
        change Except.error _ = Except.ok _ at remaining
        cases remaining
      | true =>
        have equal := scalar_passesTo_equal resultTy descriptor.ty descriptorScalar passing
        exact ⟨descriptor, declared, rfl, equal.symm⟩

#print axioms typeStatement_registerCall_result
theorem typeExpr_registerCall_tail_result (fuel : Nat) (environment : TypingEnv) (contextId origin : Nat)
    (context : Context) (callee : Impl) (arguments : List Arg) (resultTy : Ty) (before after : Nat) (types : List Ty)
    (contextAt : environment.module.contexts[contextId]? = some context)
    (calleeAt : environment.module.impls[context.impl]? = some callee)
    (results : callee.results = #[⟨resultTy, .register, none⟩])
    (scalar : (∃ intTy, resultTy = .int intTy) ∨ resultTy = .bool)
    (requests : environment.resultRequests = [.register])
    (checked : typeExpr (fuel + 1) environment (.call contextId arguments origin) before = .ok (types, after)) :
    types = [resultTy] :=
  typeExpr_registerCall_result_general fuel environment contextId origin context callee arguments resultTy before after types
    contextAt calleeAt results scalar (Or.inr requests) checked

#print axioms typeExpr_registerCall_result_general
#print axioms typeExpr_registerCall_tail_result
#print axioms typeExpr_registerCall_result
end Goose.Proofs.ConstructionAcceptedExecution
