import Goose.Proofs.ConstructionAcceptedScalarAssignCursor

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem scalarAssign_statement_cursors (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes) (place : Place)
    (expression : Expr) (origin : Nat) (form : AcceptedBinaryExpression expression)
    (next : TypingEnv) (typingAfter : Nat) (rootsAfter : RState)
    (source : AcceptedFrame config accepted frame state types)
    (initialized : frame.initialized = config.module.globals.size)
    (direct : (∃ id, place = .var id) ∨ ∃ id, place = .global id)
    (typed : typeStatement (fuel + 1) frame.typing (.assign place expression origin) frame.typingCounter = .ok (next, typingAfter))
    (rooted : rpStmt frame.source (.assign place expression origin) frame.rootCursor = .ok ((), rootsAfter)) :
    next = frame.typing ∧ typingAfter = frame.typingCounter ∧ rootsAfter.nextVar = frame.rootCursor.nextVar := by
  obtain ⟨ty, roots, expressionTypingAfter, expressionRootsAfter, checked, _, sameNext, sameAfter,
      writable, binding, placeTyped, mutable⟩ :=
    checkedValue_scalarAssign_operand fuel config accepted frame state types place expression origin form
      next typingAfter rootsAfter source initialized direct typed rooted
  have cursor := checked_binary_recursive_cursor form (scalarAssignmentOperandFrame frame fuel) ty roots
    expressionTypingAfter expressionRootsAfter checked
  have nextVar := rpStmt_directAssign_cursor frame.source place expression origin frame.rootCursor rootsAfter expressionRootsAfter
    roots direct checked.provenance rooted
  refine ⟨sameNext, ?_, ?_⟩
  · rw [sameAfter]
    simpa [scalarAssignmentOperandFrame, ordinaryOperandFrame] using cursor.1
  · rw [nextVar]
    simpa [scalarAssignmentOperandFrame, ordinaryOperandFrame] using cursor.2

#print axioms scalarAssign_statement_cursors
end Goose.Proofs.ConstructionAcceptedExecution
