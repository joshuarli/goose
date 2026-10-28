import Goose.Proofs.ConstructionAcceptedState

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem AcceptedFrame.withVisibleSubset {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types) (visible : List Nat)
    (subset : ∀ id ∈ visible, id ∈ frame.typing.visible) :
    AcceptedFrame config accepted { frame with typing := { frame.typing with visible := visible } } state types := by
  have compatible : SourceFrameCompatible accepted { frame with typing := { frame.typing with visible := visible } } := by
    refine ⟨source.compatible.module, source.compatible.rootModule, source.compatible.variables,
      source.compatible.sourceVariables, source.compatible.scopes, source.compatible.globalCount,
      source.compatible.globals, source.compatible.initialized, source.compatible.declarations,
      source.compatible.typingBound, ?_, ?_, source.compatible.currentScope, source.compatible.origin⟩
    · intro id member
      exact source.compatible.visible id (subset id member)
    · intro id initializing member
      exact source.compatible.initializing id initializing (subset id member)
  refine ⟨compatible, source.frontier, source.scopeFrontier, source.initializingBefore, source.aliases,
    ?_, ?_, source.uninitializedLocals, source.uninitializedTypes, source.futureGlobals, ?_, ?_⟩
  · intro id member
    exact source.locals id (subset id member)
  · intro id member
    exact source.localTypes id (subset id member)
  · intro id member
    exact source.direct id (subset id member)
  · intro fuel id member
    exact source.contents fuel id (subset id member)

#print axioms AcceptedFrame.withVisibleSubset
end Goose.Proofs.ConstructionAcceptedExecution
