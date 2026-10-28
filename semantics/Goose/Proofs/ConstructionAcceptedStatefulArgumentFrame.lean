import Goose.Proofs.ConstructionAcceptedStatefulCallArguments

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem AcceptedFrame.leaveSecondStatefulArgument {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {before after : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame before types) (fuel : Nat) (leftAfter : RState)
    (rootEq : leftAfter.nextVar = frame.rootCursor.nextVar)
    (child : AcceptedFrame config accepted (secondStatefulArgumentFrame frame fuel leftAfter) after types) :
    AcceptedFrame config accepted frame after types := by
  refine ⟨source.compatible, child.frontier, child.scopeFrontier, ?_, source.aliases, child.locals, child.localTypes,
    ?_, ?_, child.futureGlobals, child.direct, child.contents⟩
  · simpa [secondStatefulArgumentFrame, ordinaryOperandFrame, rootEq] using child.initializingBefore
  · simpa [secondStatefulArgumentFrame, ordinaryOperandFrame, rootEq] using child.uninitializedLocals
  · simpa [secondStatefulArgumentFrame, ordinaryOperandFrame, rootEq] using child.uninitializedTypes

#print axioms AcceptedFrame.leaveSecondStatefulArgument
end Goose.Proofs.ConstructionAcceptedExecution
