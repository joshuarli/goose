import Goose.Proofs.ConstructionAcceptedRecursiveCallCursor
import Goose.Proofs.ConstructionAcceptedRecursiveCallRootCursor
import Goose.Proofs.ConstructionAcceptedScalarLocalPrefix

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership

private theorem callLocal_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl, checked⟩

theorem typeStatement_zeroArgumentRegisterCall_cursor_nesting (fuel : Nat) (environment next : TypingEnv)
    (id contextId callOrigin origin : Nat) (before after : Nat) (context : Context) (callee : Impl) (resultTy : Ty)
    (contextAt : environment.module.contexts[contextId]? = some context)
    (calleeAt : environment.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) (results : callee.results = #[⟨resultTy, .register, none⟩])
    (scalar : (∃ intTy, resultTy = .int intTy) ∨ resultTy = .bool)
    (typed : typeStatement (fuel + 1) environment (.letS id (.call contextId [] callOrigin) origin) before = .ok (next, after)) :
    after = before + 1 ∧ 3 ≤ fuel + 1 := by
  obtain ⟨descriptor, declared, scope, order⟩ := typeStatement_let_descriptor fuel environment next id
    (.call contextId [] callOrigin) origin before after typed
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
    obtain ⟨result, expressionTyped, remaining⟩ := callLocal_bind_success _ _ _ typed
    obtain ⟨types, counter⟩ := result
    cases fuel with
    | zero =>
      change Except.error _ = Except.ok _ at expressionTyped
      cases expressionTyped
    | succ fuel =>
      cases fuel with
      | zero =>
        change typeExpr 1 { environment with use := .ordinary, request := .value, resultRequests := [] }
          (.call contextId [] callOrigin) (before + 1) = .ok (types, counter) at expressionTyped
        simp only [typeExpr, contextAt, calleeAt, bind, StateT.bind, typeArguments] at expressionTyped
        unfold_scalar_typing_helpers
        have throwState {α : Type} (error : Goose.Core.Rejection) (state : Nat) :
            (throw error : TypingM α) state = .error error := rfl
        simp [throwState, Except.bind] at expressionTyped
      | succ fuel =>
        have resultTypes := typeExpr_registerCall_result (fuel + 1)
          { environment with use := .ordinary, request := .value, resultRequests := [] }
          contextId callOrigin context callee [] resultTy (before + 1) counter types
          contextAt calleeAt results scalar rfl expressionTyped
        have cursor := typeExpr_zeroArgumentRegisterCall_cursor fuel
          { environment with use := .ordinary, request := .value, resultRequests := [] }
          contextId callOrigin context callee resultTy (before + 1) counter types
          contextAt calleeAt parameters results scalar (Or.inl rfl) expressionTyped
        subst types
        unfold_scalar_typing_helpers
        cases passing : resultTy.passesTo descriptor.ty with
        | false =>
          simp only [pure, StateT.pure, Except.pure, passing, Bool.false_eq_true, ↓reduceIte] at remaining
          change Except.error _ = Except.ok _ at remaining
          cases remaining
        | true =>
          simp only [pure, StateT.pure, Except.pure, passing, ↓reduceIte] at remaining
          cases remaining
          exact ⟨cursor, by omega⟩


theorem typeStatement_zeroArgumentRegisterCall_cursor (fuel : Nat) (environment next : TypingEnv)
    (id contextId callOrigin origin : Nat) (before after : Nat) (context : Context) (callee : Impl) (resultTy : Ty)
    (contextAt : environment.module.contexts[contextId]? = some context)
    (calleeAt : environment.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) (results : callee.results = #[⟨resultTy, .register, none⟩])
    (scalar : (∃ intTy, resultTy = .int intTy) ∨ resultTy = .bool)
    (typed : typeStatement (fuel + 1) environment (.letS id (.call contextId [] callOrigin) origin) before = .ok (next, after)) :
    after = before + 1 :=
  (typeStatement_zeroArgumentRegisterCall_cursor_nesting fuel environment next id contextId callOrigin origin before after context callee
    resultTy contextAt calleeAt parameters results scalar typed).1

theorem SourcePosition.zeroArgumentCallLocal_nesting {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes)
    (id target callOrigin origin : Nat) (rest : List Stmt) (context : Context) (callee : Impl) (ty : Ty)
    (source : AcceptedFrame config accepted frame state types)
    (position : SourcePosition accepted frame (.statements (.letS id (.call target [] callOrigin) origin :: rest)))
    (contextAt : config.module.contexts[target]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) (results : callee.results = #[⟨ty, .register, none⟩])
    (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool) : 4 ≤ frame.typingFuel := by
  obtain ⟨_, _, _, typedAll, _⟩ := position.checked accepted frame _
  cases nesting : frame.typingFuel with
  | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
  | succ headFuel =>
    cases headFuel with
    | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
    | succ checkFuel =>
      have head := position.statements_head accepted frame (.letS id (.call target [] callOrigin) origin) rest (checkFuel + 1) nesting
      obtain ⟨next, after, _, typed, _⟩ := head.checked accepted _ _
      have typingContext : frame.typing.module.contexts[target]? = some context := by simpa [source.compatible.module] using contextAt
      have typingCallee : frame.typing.module.impls[context.impl]? = some callee := by simpa [source.compatible.module] using calleeAt
      have checked := typeStatement_zeroArgumentRegisterCall_cursor_nesting checkFuel frame.typing next id target callOrigin origin
        frame.typingCounter after context callee ty typingContext typingCallee parameters results scalar typed
      omega

theorem SourcePosition.zeroArgumentCallLocal_tail {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes)
    (id target callOrigin origin checkFuel : Nat) (rest : List Stmt) (context : Context) (callee : Impl) (ty : Ty)
    (source : AcceptedFrame config accepted frame state types)
    (position : SourcePosition accepted frame (.statements (.letS id (.call target [] callOrigin) origin :: rest)))
    (nesting : frame.typingFuel = checkFuel + 2)
    (contextAt : config.module.contexts[target]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) (results : callee.results = #[⟨ty, .register, none⟩])
    (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (localScalar : ∀ descriptor, frame.typing.variables[id]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    ∃ rootsAfter,
      rpStmt frame.source (.letS id (.call target [] callOrigin) origin) frame.rootCursor = .ok ((), rootsAfter) ∧
      rootsAfter.nextVar = frame.rootCursor.nextVar + 1 ∧
      SourcePosition accepted { advanceLocalFrame { frame with typingFuel := checkFuel + 1 } id with rootCursor := rootsAfter }
        (.statements rest) := by
  have head := position.statements_head accepted frame (.letS id (.call target [] callOrigin) origin) rest (checkFuel + 1) nesting
  obtain ⟨next, typingAfter, rootsAfter, typed, rooted⟩ := head.checked accepted _ _
  have typingContext : frame.typing.module.contexts[target]? = some context := by simpa [source.compatible.module] using contextAt
  have typingCallee : frame.typing.module.impls[context.impl]? = some callee := by simpa [source.compatible.module] using calleeAt
  have nextTyping := typeStatement_let_environment checkFuel frame.typing next id (.call target [] callOrigin) origin
    frame.typingCounter typingAfter typed
  have nextCounter := typeStatement_zeroArgumentRegisterCall_cursor checkFuel frame.typing next id target callOrigin origin
    frame.typingCounter typingAfter context callee ty typingContext typingCallee parameters results scalar typed
  obtain ⟨descriptor, declared, _, _⟩ := typeStatement_let_descriptor checkFuel frame.typing next id
    (.call target [] callOrigin) origin frame.typingCounter typingAfter typed
  have sourceDeclared : frame.source.impl.vars[id]? = some descriptor := by rw [source.compatible.sourceVariables]; exact declared
  obtain ⟨order, expressionRoots, middle, expressionRooted, _⟩ := rpStmt_letS_initializer rooted
  have rootAfter := rpStmt_scalarLocal_cursor frame.source id (.call target [] callOrigin) origin frame.rootCursor
    rootsAfter middle descriptor expressionRoots sourceDeclared (localScalar descriptor declared) expressionRooted rooted
  have sourceContext : frame.source.mod.contexts[target]? = some context := by simpa [source.compatible.rootModule] using contextAt
  have sourceCallee : frame.source.mod.impls[context.impl]? = some callee := by simpa [source.compatible.rootModule] using calleeAt
  have cursor := rpExpr_zeroArgument_nextVar (env := { frame.source with initializing := id :: frame.source.initializing })
    sourceContext sourceCallee parameters expressionRooted
  have nextCursor : rootsAfter.nextVar = frame.rootCursor.nextVar + 1 := by
    rw [rootAfter]
    exact cursor
  have tail := position.statements_tail accepted frame (.letS id (.call target [] callOrigin) origin) rest
    (checkFuel + 1) next typingAfter rootsAfter nesting typed rooted
  refine ⟨rootsAfter, rooted, nextCursor, ?_⟩
  simpa [advanceLocalFrame, nextTyping, nextCounter] using tail

#print axioms SourcePosition.zeroArgumentCallLocal_nesting
#print axioms SourcePosition.zeroArgumentCallLocal_tail
#print axioms typeStatement_zeroArgumentRegisterCall_cursor_nesting
#print axioms typeStatement_zeroArgumentRegisterCall_cursor
end Goose.Proofs.ConstructionAcceptedExecution
