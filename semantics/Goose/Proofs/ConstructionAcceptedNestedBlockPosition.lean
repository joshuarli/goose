import Goose.Proofs.ConstructionAcceptedBlockTailChecks
import Goose.Proofs.ConstructionAcceptedBlockExpressionFrame
import Goose.Proofs.ConstructionAcceptedUnusedScope

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem SourcePosition.emptyBlock_nestedTail {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (scope scopeInst origin fuel : Nat) (expression : Expr)
    (nesting : frame.typingFuel = fuel + 2)
    (position : SourcePosition accepted frame (.expression (.blockE ⟨scope, [], some expression⟩ origin))) :
    ∃ expected, SourcePosition accepted (valueBlockExpressionFrame frame scope (fuel + 1) expected)
        (.block ⟨scope, [], some expression⟩) ∧ SourcePosition accepted
      (unusedChildScopeFrame (valueBlockExpressionFrame frame scope (fuel + 1) expected) scope scopeInst fuel)
      (.expression expression) := by
  obtain ⟨expected, bodyPosition⟩ := position.valueBlockExpression accepted frame scope (fuel + 1) origin [] expression
    (by simpa [Nat.add_assoc] using nesting)
  let body := valueBlockExpressionFrame frame scope (fuel + 1) expected
  obtain ⟨next, typingMiddle, rootMiddle, typed, rooted, tailPosition⟩ := bodyPosition.blockTail accepted body scope fuel [] expression rfl
  cases fuel with
  | zero => change Except.error _ = Except.ok _ at typed; cases typed
  | succ fuel =>
    have typedEq : next = { body.typing with scope := scope } ∧ typingMiddle = body.typingCounter := by
      simpa [typeStatements, pure, StateT.pure, Except.pure] using typed.symm
    have rootEq : rootMiddle = body.rootCursor := by simpa [rpStmts, pure, bind, StateT.pure, Except.pure] using rooted.symm
    obtain ⟨rfl, rfl⟩ := typedEq
    subst rootMiddle
    have actual := SourcePosition.instantiate tailPosition (body.interpretation.enterScope scope scopeInst) body.initialized
    refine ⟨expected, bodyPosition, ?_⟩
    simpa [body, unusedChildScopeFrame] using actual

#print axioms SourcePosition.emptyBlock_nestedTail
end Goose.Proofs.ConstructionAcceptedExecution
