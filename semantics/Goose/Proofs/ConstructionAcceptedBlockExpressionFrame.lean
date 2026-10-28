import Goose.Proofs.ConstructionAcceptedBlockExpressionPosition
import Goose.Proofs.ConstructionAcceptedScalarLocalAdvance

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem AcceptedFrame.valueBlockExpression {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types) (scope fuel : Nat) (expected : List Ty) :
    AcceptedFrame config accepted (valueBlockExpressionFrame frame scope fuel expected) state types := by
  let next := valueBlockExpressionFrame frame scope fuel expected
  have compatible : SourceFrameCompatible accepted next := by
    refine ⟨source.compatible.module, source.compatible.rootModule, source.compatible.variables,
      source.compatible.sourceVariables, source.compatible.scopes, source.compatible.globalCount,
      source.compatible.globals, source.compatible.initialized, source.compatible.declarations,
      source.compatible.typingBound, source.compatible.visible, source.compatible.initializing,
      source.compatible.currentScope, ?_⟩
    have origin := source.compatible.origin
    cases phase : frame.phase <;> simpa [SourceOrigin, next, valueBlockExpressionFrame, phase] using origin
  exact ⟨compatible, source.frontier, source.scopeFrontier, source.initializingBefore, source.aliases,
    source.locals, source.localTypes, source.uninitializedLocals, source.uninitializedTypes,
    source.futureGlobals, source.direct, source.contents⟩

#print axioms AcceptedFrame.valueBlockExpression
end Goose.Proofs.ConstructionAcceptedExecution
