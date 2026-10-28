import Goose.Proofs.ConstructionAcceptedScalarLocalCursor

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem AcceptedFrame.withRootCursor {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types) (cursor : RState)
    (same : cursor.nextVar = frame.rootCursor.nextVar) :
    AcceptedFrame config accepted { frame with rootCursor := cursor } state types := by
  refine ⟨⟨source.compatible.module, source.compatible.rootModule, source.compatible.variables,
    source.compatible.sourceVariables, source.compatible.scopes, source.compatible.globalCount,
    source.compatible.globals, source.compatible.initialized, ?_, source.compatible.typingBound, ?_,
    source.compatible.initializing, source.compatible.currentScope, source.compatible.origin⟩,
    source.frontier, source.scopeFrontier, ?_, source.aliases, source.locals, source.localTypes, ?_, ?_,
    source.futureGlobals, source.direct, source.contents⟩
  · simpa only [same] using source.compatible.declarations
  · simpa only [same] using source.compatible.visible
  · simpa only [same] using source.initializingBefore
  · simpa only [same] using source.uninitializedLocals
  · simpa only [same] using source.uninitializedTypes

#print axioms AcceptedFrame.withRootCursor
end Goose.Proofs.ConstructionAcceptedExecution
