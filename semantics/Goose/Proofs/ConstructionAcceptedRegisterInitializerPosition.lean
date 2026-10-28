import Goose.Proofs.ConstructionAcceptedRegisterInitializerBinding
import Goose.Proofs.ConstructionAcceptedParameterChecked

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private theorem initializer_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) : ∃ value, first = .ok value := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl⟩

theorem SourcePosition.callInitializer {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (id origin contextId callOrigin fuel : Nat) (arguments : List Arg)
    (position : SourcePosition accepted frame (.statement (.letS id (.call contextId arguments callOrigin) origin)))
    (nesting : frame.typingFuel = fuel + 1) :
    ∃ descriptor, frame.typing.variables[id]? = some descriptor ∧ id = frame.typingCounter ∧ id = frame.rootCursor.nextVar ∧
      SourcePosition accepted (letInitializerFrame frame id fuel) (.expression (.call contextId arguments callOrigin)) := by
  obtain ⟨next, counter, rootsAfter, typed, rooted⟩ := position.checked accepted frame _
  have typed' : typeStatement (fuel + 1) frame.typing (.letS id (.call contextId arguments callOrigin) origin)
      frame.typingCounter = .ok (next, counter) := by simpa [nesting] using typed
  obtain ⟨descriptor, declared, scope, order⟩ := typeStatement_let_descriptor fuel frame.typing next id
    (.call contextId arguments callOrigin) origin frame.typingCounter counter typed'
  have rootOrder := (rpStmt_letS_initializer rooted).1
  obtain ⟨_, roots, expressionRootsAfter, expressionRooted, included⟩ := rpStmt_letS_initializer rooted
  have expressionTyped : ∃ types after,
      typeExpr fuel { frame.typing with use := .ordinary, request := .value, resultRequests := [] }
        (.call contextId arguments callOrigin) (frame.typingCounter + 1) = .ok (types, after) := by
    have checked := typed'
    simp only [typeStatement, bind, StateT.bind] at checked
    subst id
    change Except.bind (((do
      let expected ← get
      if frame.typingCounter != expected then throw ⟨.type, "variables must be declared once in ascending order"⟩
      let some localVar := frame.typing.variables[frame.typingCounter]? | throw ⟨.type, "declared localVar outside table"⟩
      if localVar.scope != frame.typing.scope || !localVar.ty.storable then throw ⟨.type, "localVar scope or type mismatch"⟩
      set (expected + 1)
      pure localVar) : TypingM LocalVar) frame.typingCounter) _ = _ at checked
    have getState (state : Nat) : (get : TypingM Nat) state = .ok (state, state) := rfl
    have setState (next state : Nat) : (set next : TypingM Unit) state = .ok ((), next) := rfl
    simp only [bind, StateT.bind, getState, Except.bind, bne_self_eq_false, declared, scope,
      bne_self_eq_false, Bool.false_or] at checked
    cases storable : descriptor.ty.storable with
    | false =>
      simp only [storable, Bool.not_false, ↓reduceIte] at checked
      change Except.error _ = Except.ok _ at checked
      cases checked
    | true =>
      simp only [storable, Bool.not_true, pure, StateT.pure, Except.pure] at checked
      obtain ⟨result, expressionChecked⟩ := initializer_bind_success _ _ _ checked
      exact ⟨result.1, result.2, expressionChecked⟩
  obtain ⟨types, after, expressionChecked⟩ := expressionTyped
  refine ⟨descriptor, declared, order, rootOrder, .child position (.letInitializer frame id origin fuel _ nesting order rootOrder) ?_⟩
  exact ⟨types, after, roots, expressionRootsAfter, by simpa [letInitializerFrame, ordinaryOperandFrame] using expressionChecked,
    by simpa [letInitializerFrame, ordinaryOperandFrame] using expressionRooted⟩


theorem SourcePosition.registerCallInitializer {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (id origin contextId callOrigin fuel : Nat) (expression : Expr)
    (position : SourcePosition accepted frame (.statement (.letS id (.call contextId [.byVal expression] callOrigin) origin)))
    (nesting : frame.typingFuel = fuel + 1) :
    ∃ descriptor, frame.typing.variables[id]? = some descriptor ∧ id = frame.typingCounter ∧ id = frame.rootCursor.nextVar ∧
      SourcePosition accepted (letInitializerFrame frame id fuel) (.expression (.call contextId [.byVal expression] callOrigin)) := by
  exact position.callInitializer frame id origin contextId callOrigin fuel [.byVal expression] nesting

theorem checkedRegisterCallInitializerArgument {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes)
    (localId origin contextId callOrigin checkFuel : Nat) (expression : Expr)
    (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
    (source : AcceptedFrame config accepted frame state types)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (mode : parameter.mode = .byValue)
    (declared : callee.vars[parameter.var]? = some descriptor)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (form : AcceptedBinaryExpression expression)
    (initialized : frame.initialized = config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size)
    (nesting : frame.typingFuel = checkFuel + 3)
    (position : SourcePosition accepted frame (.statement (.letS localId (.call contextId [.byVal expression] callOrigin) origin))) :
    ∃ localDescriptor roots typingAfter rootsAfter,
      frame.typing.variables[localId]? = some localDescriptor ∧ localId = frame.typingCounter ∧
      localId = frame.rootCursor.nextVar ∧
      CheckedValue (letInitializerFrame frame localId checkFuel) expression descriptor.ty roots typingAfter rootsAfter := by
  obtain ⟨localDescriptor, localDeclared, typingOrder, rootOrder, callPosition⟩ :=
    position.registerCallInitializer frame localId origin contextId callOrigin (checkFuel + 2) expression (by omega)
  let initial := letInitializerFrame frame localId (checkFuel + 2)
  have initialSource := source.letInitializer localId (checkFuel + 2) localDescriptor rootOrder typingOrder localDeclared
  have initialBound : GlobalEffectTargetsBounded initial.rootCursor.eff config.module.globals.size := by
    simpa [initial, letInitializerFrame, ordinaryOperandFrame] using bounded
  obtain ⟨roots, typingAfter, rootsAfter, checked⟩ := checkedScalarCallArgument initial contextId context callee parameter descriptor
    expression callOrigin checkFuel initialSource.compatible contextAt calleeAt parameters mode declared scalar form initialized
    initialBound rfl callPosition
  exact ⟨localDescriptor, roots, typingAfter, rootsAfter, localDeclared, typingOrder, rootOrder,
    by simpa [initial, letInitializerFrame, ordinaryOperandFrame] using checked⟩

#print axioms checkedRegisterCallInitializerArgument
#print axioms SourcePosition.callInitializer
#print axioms SourcePosition.registerCallInitializer
end Goose.Proofs.ConstructionAcceptedExecution
