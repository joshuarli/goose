import Goose.Proofs.ConstructionAcceptedScalarInitializer

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem AcceptedFrame.leaveLetInitializer {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {before after : ExecutionState} {types nextTypes : RootTypes}
    (source : AcceptedFrame config accepted frame before types) (localId fuel : Nat)
    (rootOrder : localId = frame.rootCursor.nextVar)
    (child : AcceptedFrame config accepted (letInitializerFrame frame localId fuel) after nextTypes) :
    AcceptedFrame config accepted frame after nextTypes := by
  refine ⟨source.compatible, child.frontier, child.scopeFrontier, source.initializingBefore, source.aliases,
    child.locals, child.localTypes, ?_, ?_, child.futureGlobals, child.direct, child.contents⟩
  · intro id condition root resolved
    apply child.uninitializedLocals id ?_ root resolved
    rcases condition with later | initializing
    · by_cases same : id = localId
      · right; simp [letInitializerFrame, same]
      · left; simp only [letInitializerFrame, ordinaryOperandFrame]
        rw [rootOrder] at same
        omega
    · right; simp [letInitializerFrame, initializing]
  · intro id condition root resolved
    apply child.uninitializedTypes id ?_ root resolved
    rcases condition with later | initializing
    · by_cases same : id = localId
      · right; simp [letInitializerFrame, same]
      · left; simp only [letInitializerFrame, ordinaryOperandFrame]
        rw [rootOrder] at same
        omega
    · right; simp [letInitializerFrame, initializing]

#print axioms AcceptedFrame.leaveLetInitializer
end Goose.Proofs.ConstructionAcceptedExecution
