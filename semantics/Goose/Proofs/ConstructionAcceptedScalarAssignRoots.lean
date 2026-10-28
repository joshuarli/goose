import Goose.Proofs.ConstructionAcceptedScalarAssignTyping
import Lean.Elab.Tactic

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private def assignRootsHelperName (name : String) : Lean.Name :=
  Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Goose") "Construct") "Roots") 0) "Goose") "Construct") name

elab "unfold_assign_roots_helpers" : tactic => do
  let capture := Lean.mkIdent (assignRootsHelperName "captureEffects")
  let named := Lean.mkIdent (assignRootsHelperName "noteNamed")
  Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $capture $named at *))

theorem rpStmt_directAssign_operand (env : PEnv) (place : Place) (expression : Expr) (origin : Goose.Core.OriginId)
    (before after : RState) (direct : (∃ id, place = .var id) ∨ ∃ id, place = .global id)
    (checked : rpStmt env (.assign place expression origin) before = .ok ((), after)) :
    ∃ roots middle, rpExpr env expression { before with eff := {} } = .ok (roots, middle) := by
  rcases direct with ⟨id, rfl⟩ | ⟨id, rfl⟩ <;>
    simp only [rpStmt, rpPlace, bind, StateT.bind] at checked <;>
    unfold_assign_roots_helpers
  all_goals
    cases operand : rpExpr env expression { before with eff := {} } with
    | ok pair => exact ⟨pair.1, pair.2, rfl⟩
    | error failure =>
      have modifyState (f : RState → RState) (state : RState) : (modify f : P Unit) state = .ok ((), f state) := rfl
      simp [bind, StateT.bind, modifyState, pure, StateT.pure, Except.pure, Except.bind, operand] at checked

def scalarAssignmentOperandFrame (frame : ConstructionSourceFrame) (fuel : Nat) : ConstructionSourceFrame :=
  { ordinaryOperandFrame frame fuel with rootCursor := { frame.rootCursor with eff := {} } }

theorem checkedValue_scalarAssign_operand (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes) (place : Place)
    (expression : Expr) (origin : Goose.Core.OriginId) (form : AcceptedBinaryExpression expression)
    (next : TypingEnv) (typingAfter : Nat) (rootsAfter : RState)
    (source : AcceptedFrame config accepted frame state types)
    (initialized : frame.initialized = config.module.globals.size)
    (direct : (∃ id, place = .var id) ∨ ∃ id, place = .global id)
    (typed : typeStatement (fuel + 1) frame.typing (.assign place expression origin) frame.typingCounter = .ok (next, typingAfter))
    (rooted : rpStmt frame.source (.assign place expression origin) frame.rootCursor = .ok ((), rootsAfter)) :
    ∃ ty roots expressionTypingAfter expressionRootsAfter,
      CheckedValue (scalarAssignmentOperandFrame frame fuel) expression ty roots expressionTypingAfter expressionRootsAfter ∧
      AcceptedFrame config accepted (scalarAssignmentOperandFrame frame fuel) state types ∧
      next = frame.typing ∧ typingAfter = expressionTypingAfter ∧
      ∃ writable binding, typePlace fuel frame.typing place frame.typingCounter =
        .ok ((ty, writable, binding), frame.typingCounter) ∧ writable = true := by
  obtain ⟨ty, writable, binding, middle, expressionAfter, placeTyped, expressionTyped, flat, mutable, sameNext, sameAfter⟩ :=
    typeStatement_scalarAssign fuel frame.typing next place expression origin frame.typingCounter typingAfter form typed
  have sameMiddle : middle = frame.typingCounter := by
    rcases direct with ⟨id, same⟩ | ⟨id, same⟩
    · subst place
      obtain ⟨descriptor, visible, declared, sameTy, sameMutable, sameMiddle⟩ :=
        typePlace_local_scalarFacts fuel frame.typing id frame.typingCounter middle ty writable binding placeTyped
      exact sameMiddle
    · subst place
      obtain ⟨descriptor, inside, declared, sameTy, sameMutable, sameMiddle⟩ :=
        typePlace_global_scalarFacts fuel frame.typing id frame.typingCounter middle ty writable binding placeTyped
      exact sameMiddle
  subst middle
  obtain ⟨roots, expressionRootsAfter, expressionRooted⟩ := rpStmt_directAssign_operand frame.source place expression origin
    frame.rootCursor rootsAfter direct rooted
  have initial := (ordinaryOperandFrame_accepted accepted frame fuel state types source).withRootCursor
    { frame.rootCursor with eff := {} } rfl
  have bound : GlobalEffectTargetsBounded (scalarAssignmentOperandFrame frame fuel).rootCursor.eff config.module.globals.size := by
    simp [scalarAssignmentOperandFrame, GlobalEffectTargetsBounded, Eff.accessTargets]
  have effects : GlobalEffectTargetsBounded expressionRootsAfter.eff config.module.globals.size := by
    exact recursiveScalar_effects_bounded form fuel (scalarAssignmentOperandFrame frame fuel).typing
      (scalarAssignmentOperandFrame frame fuel).source config.module.globals.size frame.typingCounter expressionAfter
      (scalarAssignmentOperandFrame frame fuel).rootCursor expressionRootsAfter [ty] roots source.compatible.globals
      bound expressionTyped expressionRooted
  have available : GlobalEffectsAvailable frame.interpretation frame.initialized expressionRootsAfter.eff := by
    rw [initialized, ← source.compatible.globalCount]
    exact (globalEffectsAvailable_iff_bounded frame.interpretation expressionRootsAfter.eff).2
      (by simpa only [source.compatible.globalCount] using effects)
  exact ⟨ty, roots, expressionAfter, expressionRootsAfter, ⟨expressionTyped, expressionRooted, available⟩,
    initial, sameNext, sameAfter, writable, binding, placeTyped, mutable⟩

#print axioms checkedValue_scalarAssign_operand
#print axioms rpStmt_directAssign_operand
end Goose.Proofs.ConstructionAcceptedExecution
