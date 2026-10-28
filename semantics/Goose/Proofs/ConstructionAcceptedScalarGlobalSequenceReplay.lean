import Goose.Proofs.ConstructionAcceptedScalarAssignCursor
import Goose.Proofs.ConstructionByteReplay

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

inductive ScalarGlobalAssignments : List Stmt → Prop where
  | nil : ScalarGlobalAssignments []
  | cons (id : Nat) (expression : Expr) (origin : Nat) (rest : List Stmt) :
      AcceptedBinaryExpression expression → ScalarGlobalAssignments rest →
      ScalarGlobalAssignments (.assign (.global id) expression origin :: rest)

theorem SourcePosition.scalarGlobalAssignments_replay {statements : List Stmt}
    (form : ScalarGlobalAssignments statements) :
    ∀ {config : EvalConfig} (accepted : AcceptedModule config)
      (frame : ConstructionSourceFrame) (before : ExecutionState) (types : RootTypes),
      AcceptedFrame config accepted frame before types →
      frame.initialized = config.module.globals.size →
      GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size →
      SourcePosition accepted frame (.statements statements) →
      ∃ rootsAfter, rootsAfter.nextVar = frame.rootCursor.nextVar ∧
        GlobalEffectTargetsBounded rootsAfter.eff config.module.globals.size ∧
        typeStatements frame.typingFuel frame.typing statements frame.typingCounter = .ok (frame.typing, frame.typingCounter) ∧
        rpStmts frame.source statements frame.rootCursor = .ok ((), rootsAfter) := by
  induction form with
  | nil =>
    intro config accepted frame before types source initialized bounded position
    obtain ⟨_, _, _, typed, _⟩ := position.checked accepted frame _
    cases nesting : frame.typingFuel with
    | zero => rw [nesting] at typed; change Except.error _ = Except.ok _ at typed; cases typed
    | succ fuel =>
      exact ⟨frame.rootCursor, rfl, bounded, by simp [typeStatements, pure, StateT.pure, Except.pure], rfl⟩
  | cons id expression origin rest expressionForm restForm ih =>
    intro config accepted frame before types source initialized bounded position
    obtain ⟨_, _, _, typedAll, _⟩ := position.checked accepted frame _
    cases nesting : frame.typingFuel with
    | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
    | succ headFuel =>
      cases headFuel with
      | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
      | succ checkFuel =>
        have nesting' : frame.typingFuel = checkFuel + 2 := by omega
        obtain ⟨middleRoots, sameRoot, middleBounded, headTyped, headRooted, tailPosition⟩ :=
          position.scalarAssign_tailReplay accepted frame before types (.global id) expression origin rest checkFuel
            expressionForm source initialized bounded nesting' (Or.inr ⟨id, rfl⟩)
        let middle := { frame with typingFuel := checkFuel + 1, rootCursor := middleRoots }
        have middleSource : AcceptedFrame config accepted middle before types :=
          (source.withTypingFuel (checkFuel + 1)).withRootCursor middleRoots sameRoot
        obtain ⟨finalRoots, finalSame, finalBounded, tailTyped, tailRooted⟩ :=
          ih accepted middle before types middleSource initialized middleBounded tailPosition
        have replay := statementReplay_cons (checkFuel + 1) frame middle
          { middle with rootCursor := finalRoots } (.assign (.global id) expression origin) rest
          headTyped headRooted rfl tailTyped tailRooted
        exact ⟨finalRoots, finalSame.trans sameRoot, finalBounded, by simpa [middle, nesting'] using replay.1,
          by simpa [middle] using replay.2⟩

#print axioms SourcePosition.scalarGlobalAssignments_replay
end Goose.Proofs.ConstructionAcceptedExecution
