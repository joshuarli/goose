import Goose.Proofs.ConstructionAcceptedScalarLocalTyping

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem scalar_passesTo_equal (source target : Ty)
    (scalar : (∃ ty, target = .int ty) ∨ target = .bool) (passing : source.passesTo target = true) :
    source = target := by
  rcases scalar with ⟨ty, rfl⟩ | rfl <;> cases source <;>
    simp [Ty.passesTo, Ty.adaptsTo, Ty.element?] at passing ⊢ <;> assumption

theorem rpStmt_scalarLocal_cursor (env : PEnv) (id : Nat) (expression : Expr) (origin : Goose.Core.OriginId)
    (before after middle : RState) (descriptor : LocalVar) (roots : List RootRef)
    (declared : env.impl.vars[id]? = some descriptor)
    (scalar : (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (operand : rpExpr { env with initializing := id :: env.initializing } expression
      { before with nextVar := before.nextVar + 1 } = .ok (roots, middle))
    (checked : rpStmt env (.letS id expression origin) before = .ok ((), after)) :
    after = middle := by
  have order := (rpStmt_letS_initializer checked).1
  subst id
  simp only [rpStmt, bind, StateT.bind] at checked
  have getState (state : RState) : (get : P RState) state = .ok (state, state) := rfl
  have modifyState (f : RState → RState) (state : RState) : (modify f : P Unit) state = .ok ((), f state) := rfl
  simp only [getState, Except.bind, ↓reduceIte] at checked
  simp only [StateT.bind, modifyState, declared] at checked
  rcases scalar with ⟨ty, same⟩ | same <;> simp only [same, Ty.isRefLike] at checked
  all_goals
    simp [bind, Except.bind, operand, pure] at checked
    change Except.ok ((), middle) = Except.ok ((), after) at checked
    cases checked
    rfl

theorem checkedValue_typedScalarLocal_initializer (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes)
    (id : Nat) (expression : Expr) (origin : Goose.Core.OriginId) (form : AcceptedBinaryExpression expression)
    (next : TypingEnv) (typingAfter : Nat) (rootsAfter : RState)
    (source : AcceptedFrame config accepted frame state types)
    (initialized : frame.initialized = config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size)
    (typed : typeStatement (fuel + 1) frame.typing (.letS id expression origin) frame.typingCounter = .ok (next, typingAfter))
    (rooted : rpStmt frame.source (.letS id expression origin) frame.rootCursor = .ok ((), rootsAfter))
    (scalar : ∀ descriptor, frame.typing.variables[id]? = some descriptor →
      (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool) :
    ∃ descriptor roots expressionTypingAfter expressionRootsAfter,
      frame.typing.variables[id]? = some descriptor ∧
      CheckedValue (letInitializerFrame frame id fuel) expression descriptor.ty roots expressionTypingAfter expressionRootsAfter ∧
      AcceptedFrame config accepted (letInitializerFrame frame id fuel) state types := by
  obtain ⟨descriptor, ty, roots, expressionTypingAfter, expressionRootsAfter, declared, passing, checked, initializer⟩ :=
    checkedValue_scalarLocal_initializer fuel config accepted frame state types id expression origin form next typingAfter rootsAfter
      source initialized bounded typed rooted
  have equal := scalar_passesTo_equal ty descriptor.ty (scalar descriptor declared) passing
  subst ty
  exact ⟨descriptor, roots, expressionTypingAfter, expressionRootsAfter, declared, checked, initializer⟩

#print axioms checkedValue_typedScalarLocal_initializer
#print axioms scalar_passesTo_equal
#print axioms rpStmt_scalarLocal_cursor
end Goose.Proofs.ConstructionAcceptedExecution
