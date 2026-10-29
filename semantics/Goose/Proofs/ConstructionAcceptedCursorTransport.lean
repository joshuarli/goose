import Goose.Proofs.ConstructionAcceptedState

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem AcceptedFrame.with_rootCursor {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types) (cursor : RState)
    (nextVar : cursor.nextVar = frame.rootCursor.nextVar) :
    AcceptedFrame config accepted { frame with rootCursor := cursor } state types := by
  have compatible : SourceFrameCompatible accepted { frame with rootCursor := cursor } := by
    refine ⟨source.compatible.module, source.compatible.rootModule, source.compatible.variables,
      source.compatible.sourceVariables, source.compatible.scopes, source.compatible.globalCount,
      source.compatible.globals, source.compatible.initialized, ?_, source.compatible.typingBound,
      ?_, source.compatible.initializing, source.compatible.currentScope, source.compatible.origin⟩
    · simpa only [nextVar] using source.compatible.declarations
    · simpa only [nextVar] using source.compatible.visible
  refine ⟨compatible, source.frontier, source.scopeFrontier, ?_, source.aliases, source.locals,
    source.localTypes, ?_, ?_, source.futureGlobals, source.direct, source.contents⟩
  · simpa only [nextVar] using source.initializingBefore
  · simpa only [nextVar] using source.uninitializedLocals
  · simpa only [nextVar] using source.uninitializedTypes

#print axioms AcceptedFrame.with_rootCursor
end Goose.Proofs.ConstructionAcceptedExecution
