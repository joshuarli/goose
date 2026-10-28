import Goose.Proofs.ConstructionAcceptedScalarInitializer
import Lean.Elab.Tactic

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership

private def typingHelperName (name : String) : Lean.Name :=
  Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Goose") "Construct") "Typing") 0) "Goose") "Construct") name

elab "unfold_scalar_typing_helpers" : tactic => do
  let one := Lean.mkIdent (typingHelperName "one")
  let require := Lean.mkIdent (typingHelperName "require")
  let fail := Lean.mkIdent (typingHelperName "fail")
  Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $one $require $fail at *))

private theorem scalarLocal_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl, checked⟩

theorem typeStatement_scalarLocal_initializer (fuel : Nat) (environment next : TypingEnv) (id : Nat)
    (expression : Expr) (origin before after : Nat) (form : AcceptedBinaryExpression expression)
    (typed : typeStatement (fuel + 1) environment (.letS id expression origin) before = .ok (next, after)) :
    ∃ descriptor ty typingAfter, environment.variables[id]? = some descriptor ∧ id = before ∧
      typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] } expression (before + 1) = .ok ([ty], typingAfter) ∧
      ty.passesTo descriptor.ty = true := by
  obtain ⟨descriptor, declared, scope, order⟩ := typeStatement_let_descriptor fuel environment next id expression origin before after typed
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
    obtain ⟨result, expressionTyped, remaining⟩ := scalarLocal_bind_success _ _ _ typed
    obtain ⟨resultTypes, typingAfter⟩ := result
    obtain ⟨ty, sameTypes⟩ := typeExpr_scalar_singleton form fuel { environment with use := .ordinary, request := .value, resultRequests := [] } (before + 1) typingAfter resultTypes expressionTyped
    subst resultTypes
    refine ⟨descriptor, ty, typingAfter, declared, rfl, expressionTyped, ?_⟩
    unfold_scalar_typing_helpers
    cases passing : ty.passesTo descriptor.ty with
    | true => rfl
    | false =>
      simp only [pure, StateT.pure, Except.pure, passing, Bool.false_eq_true, ↓reduceIte] at remaining
      change Except.error _ = Except.ok _ at remaining
      cases remaining

theorem checkedValue_scalarLocal_initializer (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes)
    (id : Nat) (expression : Expr) (origin : Goose.Core.OriginId) (form : AcceptedBinaryExpression expression)
    (next : TypingEnv) (typingAfter : Nat) (rootsAfter : RState)
    (source : AcceptedFrame config accepted frame state types)
    (initialized : frame.initialized = config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size)
    (typed : typeStatement (fuel + 1) frame.typing (.letS id expression origin) frame.typingCounter = .ok (next, typingAfter))
    (rooted : rpStmt frame.source (.letS id expression origin) frame.rootCursor = .ok ((), rootsAfter)) :
    ∃ descriptor ty roots expressionTypingAfter expressionRootsAfter,
      frame.typing.variables[id]? = some descriptor ∧ ty.passesTo descriptor.ty = true ∧
      CheckedValue (letInitializerFrame frame id fuel) expression ty roots expressionTypingAfter expressionRootsAfter ∧
      AcceptedFrame config accepted (letInitializerFrame frame id fuel) state types := by
  obtain ⟨descriptor, ty, expressionTypingAfter, declared, typingOrder, expressionTyped, passing⟩ :=
    typeStatement_scalarLocal_initializer fuel frame.typing next id expression origin frame.typingCounter typingAfter form typed
  obtain ⟨rootOrder, roots, expressionRootsAfter, expressionRooted, included⟩ := rpStmt_letS_initializer rooted
  have initializer := source.letInitializer id fuel descriptor rootOrder typingOrder declared
  have effects : GlobalEffectTargetsBounded expressionRootsAfter.eff config.module.globals.size := by
    exact recursiveScalar_effects_bounded form fuel (letInitializerFrame frame id fuel).typing
      (letInitializerFrame frame id fuel).source config.module.globals.size (frame.typingCounter + 1) expressionTypingAfter
      (letInitializerFrame frame id fuel).rootCursor expressionRootsAfter [ty] roots source.compatible.globals
      bounded expressionTyped expressionRooted
  have available : GlobalEffectsAvailable (letInitializerFrame frame id fuel).interpretation
      (letInitializerFrame frame id fuel).initialized expressionRootsAfter.eff := by
    change GlobalEffectsAvailable frame.interpretation frame.initialized expressionRootsAfter.eff
    rw [initialized, ← source.compatible.globalCount]
    exact (globalEffectsAvailable_iff_bounded frame.interpretation expressionRootsAfter.eff).2
      (by simpa only [source.compatible.globalCount] using effects)
  exact ⟨descriptor, ty, roots, expressionTypingAfter, expressionRootsAfter, declared, passing,
    ⟨expressionTyped, expressionRooted, available⟩, initializer⟩

#print axioms checkedValue_scalarLocal_initializer
#print axioms typeStatement_scalarLocal_initializer
end Goose.Proofs.ConstructionAcceptedExecution
