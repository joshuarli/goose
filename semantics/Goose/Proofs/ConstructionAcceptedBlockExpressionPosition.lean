import Goose.Proofs.ConstructionAcceptedBlockExpressionRoots
import Goose.Proofs.ConstructionAcceptedPositions

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem SourcePosition.valueBlockExpression {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (scope fuel origin : Nat) (statements : List Stmt) (tail : Expr)
    (position : SourcePosition accepted frame (.expression (.blockE ⟨scope, statements, some tail⟩ origin)))
    (nesting : frame.typingFuel = fuel + 1) :
    ∃ expected, SourcePosition accepted (valueBlockExpressionFrame frame scope fuel expected)
      (.block ⟨scope, statements, some tail⟩) := by
  obtain ⟨types, typingAfter, roots, rootsAfter, typed, rooted⟩ := position.checked accepted frame _
  rw [nesting] at typed
  obtain ⟨expected, query, bodyTyped, same⟩ := typeExpr_blockE_tail fuel frame.typing scope statements tail origin
    frame.typingCounter typingAfter types typed
  obtain ⟨start, finish, bodyAfter, bodyRooted, restored⟩ := rpExpr_blockE_body frame.source scope statements
    (some tail) origin frame.rootCursor rootsAfter roots rooted
  refine ⟨expected, .child position (.valueBlockExpression frame scope fuel origin statements tail expected nesting query) ?_⟩
  exact ⟨types, typingAfter, (roots, (start, finish)), bodyAfter, bodyTyped, bodyRooted⟩

#print axioms SourcePosition.valueBlockExpression
end Goose.Proofs.ConstructionAcceptedExecution
