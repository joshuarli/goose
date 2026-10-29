import Goose.Proofs.ConstructionAcceptedCallLocalCursor
import Goose.Proofs.ConstructionAcceptedRecursiveCallRootCursor
import Goose.Proofs.ConstructionAcceptedCursorTransport

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

elab "unfold_byte_call_require" : tactic => do
  let name := Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Goose") "Construct") "Typing") 0) "Goose") "Construct") "require"
  let require := Lean.mkIdent name
  Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $require at *))

private theorem byteCall_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl, checked⟩

theorem typeExpr_zeroArgumentByteCall_cursor (fuel : Nat) (environment : TypingEnv) (contextId origin : Nat)
    (context : Context) (callee : Impl) (before after : Nat) (types : List Ty)
    (contextAt : environment.module.contexts[contextId]? = some context)
    (calleeAt : environment.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) (results : callee.results = #[⟨.varr (.int .u8), .value, none⟩])
    (requests : environment.resultRequests = []) (request : environment.request = .value)
    (checked : typeExpr (fuel + 2) environment (.call contextId [] origin) before = .ok (types, after)) :
    after = before := by
  simp only [typeExpr, contextAt, calleeAt, parameters, typeArguments] at checked
  unfold_byte_call_require
  simp [results, requests, request, Ty.nonfixed, bind, StateT.bind, pure, StateT.pure, Except.pure] at checked
  cases checked
  rfl

theorem typeStatement_zeroArgumentByteCall_cursor (fuel : Nat) (environment next : TypingEnv)
    (id contextId callOrigin origin : Nat) (before after : Nat) (context : Context) (callee : Impl)
    (contextAt : environment.module.contexts[contextId]? = some context)
    (calleeAt : environment.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) (results : callee.results = #[⟨.varr (.int .u8), .value, none⟩])
    (typed : typeStatement (fuel + 1) environment (.letS id (.call contextId [] callOrigin) origin) before = .ok (next, after)) :
    after = before + 1 := by
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
    obtain ⟨result, expressionTyped, remaining⟩ := byteCall_bind_success _ _ _ typed
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
        have cursor := typeExpr_zeroArgumentByteCall_cursor fuel
          { environment with use := .ordinary, request := .value, resultRequests := [] }
          contextId callOrigin context callee (before + 1) counter types
          contextAt calleeAt parameters results rfl rfl expressionTyped
        unfold_scalar_typing_helpers
        have throwState {α : Type} (error : Goose.Core.Rejection) (state : Nat) :
            (throw error : TypingM α) state = .error error := rfl
        cases types with
        | nil => simp [throwState] at remaining
        | cons ty rest =>
          cases rest with
          | cons other rest => simp [throwState] at remaining
          | nil =>
            cases passing : ty.passesTo descriptor.ty with
            | false => simp [pure, StateT.pure, Except.pure, passing, throwState] at remaining
            | true =>
              simp only [pure, StateT.pure, Except.pure, passing, ↓reduceIte] at remaining
              cases remaining
              exact cursor

theorem rpStmt_zeroArgumentByteCall_nextVar (env : PEnv) (id contextId callOrigin origin : Nat)
    (before after : RState) (descriptor : LocalVar) (context : Context) (callee : Impl)
    (declared : env.impl.vars[id]? = some descriptor) (descriptorType : descriptor.ty = .varr (.int .u8))
    (contextAt : env.mod.contexts[contextId]? = some context)
    (calleeAt : env.mod.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) (results : callee.results = #[⟨.varr (.int .u8), .value, none⟩])
    (checked : rpStmt env (.letS id (.call contextId [] callOrigin) origin) before = .ok ((), after)) :
    after.nextVar = before.nextVar + 1 := by
  obtain ⟨order, roots, middle, operand, _⟩ := rpStmt_letS_initializer checked
  have next := rpExpr_zeroArgument_nextVar (env := { env with initializing := id :: env.initializing })
    contextAt calleeAt parameters operand
  subst id
  simp only [rpStmt, bind, StateT.bind] at checked
  have getState (state : RState) : (get : P RState) state = .ok (state, state) := rfl
  have modifyState (f : RState → RState) (state : RState) : (modify f : P Unit) state = .ok ((), f state) := rfl
  simp only [getState, Except.bind, ↓reduceIte, StateT.bind, modifyState, operand, declared,
    descriptorType, Ty.isRefLike, Bool.false_eq_true, ↓reduceIte,
    noteReceivingCapacity_call_byte_result env contextId callOrigin context callee contextAt calleeAt results,
    bind, pure, StateT.pure, Except.pure] at checked
  cases checked
  exact next

theorem SourcePosition.zeroArgumentByteCallLocal_tail {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes)
    (id target callOrigin origin checkFuel : Nat) (rest : List Stmt) (context : Context) (callee : Impl)
    (source : AcceptedFrame config accepted frame state types)
    (position : SourcePosition accepted frame (.statements (.letS id (.call target [] callOrigin) origin :: rest)))
    (nesting : frame.typingFuel = checkFuel + 2)
    (contextAt : config.module.contexts[target]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) (results : callee.results = #[⟨.varr (.int .u8), .value, none⟩])
    (owner : (frame.source.impl.vars[id]?).map (·.ty) = some (.varr (.int .u8))) :
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
  have nextCounter := typeStatement_zeroArgumentByteCall_cursor checkFuel frame.typing next id target callOrigin origin
    frame.typingCounter typingAfter context callee typingContext typingCallee parameters results typed
  obtain ⟨descriptor, declared, _, _⟩ := typeStatement_let_descriptor checkFuel frame.typing next id
    (.call target [] callOrigin) origin frame.typingCounter typingAfter typed
  have sourceDeclared : frame.source.impl.vars[id]? = some descriptor := by rw [source.compatible.sourceVariables]; exact declared
  have descriptorType : descriptor.ty = .varr (.int .u8) := by simpa only [sourceDeclared, Option.map_some, Option.some.injEq] using owner
  have sourceContext : frame.source.mod.contexts[target]? = some context := by simpa [source.compatible.rootModule] using contextAt
  have sourceCallee : frame.source.mod.impls[context.impl]? = some callee := by simpa [source.compatible.rootModule] using calleeAt
  have nextCursor := rpStmt_zeroArgumentByteCall_nextVar frame.source id target callOrigin origin frame.rootCursor rootsAfter
    descriptor context callee sourceDeclared descriptorType sourceContext sourceCallee parameters results rooted
  have tail := position.statements_tail accepted frame (.letS id (.call target [] callOrigin) origin) rest
    (checkFuel + 1) next typingAfter rootsAfter nesting typed rooted
  refine ⟨rootsAfter, rooted, nextCursor, ?_⟩
  simpa [advanceLocalFrame, nextTyping, nextCounter] using tail

#print axioms SourcePosition.zeroArgumentByteCallLocal_tail
#print axioms rpStmt_zeroArgumentByteCall_nextVar
#print axioms noteReceivingCapacity_call_byte_result
#print axioms typeExpr_zeroArgumentByteCall_cursor
#print axioms typeStatement_zeroArgumentByteCall_cursor
end Goose.Proofs.ConstructionAcceptedExecution
