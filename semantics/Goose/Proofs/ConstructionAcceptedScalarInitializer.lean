import Goose.Proofs.ConstructionAcceptedScalarBinding

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem AcceptedFrame.letInitializer {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types) (id fuel : Nat) (descriptor : LocalVar)
    (rootOrder : id = frame.rootCursor.nextVar) (typingOrder : id = frame.typingCounter)
    (declared : frame.typing.variables[id]? = some descriptor) :
    AcceptedFrame config accepted (letInitializerFrame frame id fuel) state types := by
  have base := ordinaryOperandFrame_accepted accepted frame fuel state types source
  have bound := (Array.getElem?_eq_some_iff.mp declared).1
  have idNotVisible : id ∉ frame.typing.visible := by
    intro present
    have earlier := source.compatible.visible id present
    rw [rootOrder] at earlier
    exact (Nat.lt_irrefl _ earlier).elim
  refine ⟨⟨base.compatible.module, base.compatible.rootModule, base.compatible.variables,
    base.compatible.sourceVariables, base.compatible.scopes, base.compatible.globalCount,
    base.compatible.globals, base.compatible.initialized, ?_, ?_, ?_, ?_, base.compatible.currentScope, ?_⟩,
    base.frontier, base.scopeFrontier, ?_, base.aliases, base.locals, base.localTypes, ?_, ?_,
    base.futureGlobals, base.direct, base.contents⟩
  · change frame.rootCursor.nextVar + 1 ≤ frame.typingCounter + 1
    exact Nat.succ_le_succ source.compatible.declarations
  · change frame.typingCounter + 1 ≤ frame.typing.variables.size
    rw [← typingOrder]; omega
  · intro other member
    change other < frame.rootCursor.nextVar + 1
    exact Nat.lt_trans (source.compatible.visible other member) (Nat.lt_succ_self _)
  · intro other member
    change other ∈ id :: frame.source.initializing at member
    rcases List.mem_cons.mp member with same | old
    · simpa [letInitializerFrame, ordinaryOperandFrame, same] using idNotVisible
    · exact source.compatible.initializing other old
  · simpa [SourceOrigin, letInitializerFrame, ordinaryOperandFrame] using source.compatible.origin
  · intro other member
    change other ∈ id :: frame.source.initializing at member
    change other < frame.rootCursor.nextVar + 1
    rcases List.mem_cons.mp member with same | old
    · simp [same, rootOrder]
    · exact Nat.lt_trans (source.initializingBefore other old) (Nat.lt_succ_self _)
  · intro other condition root resolved
    change frame.rootCursor.nextVar + 1 ≤ other ∨ other ∈ id :: frame.source.initializing at condition
    have oldCondition : frame.rootCursor.nextVar ≤ other ∨ other ∈ frame.source.initializing := by
      rcases condition with future | initializing
      · exact Or.inl (Nat.le_trans (Nat.le_succ _) future)
      · rcases List.mem_cons.mp initializing with same | old
        · exact Or.inl (by rw [same, rootOrder]; omega)
        · exact Or.inr old
    exact source.uninitializedLocals other oldCondition root resolved
  · intro other condition root resolved
    change frame.rootCursor.nextVar + 1 ≤ other ∨ other ∈ id :: frame.source.initializing at condition
    have oldCondition : frame.rootCursor.nextVar ≤ other ∨ other ∈ frame.source.initializing := by
      rcases condition with future | initializing
      · exact Or.inl (Nat.le_trans (Nat.le_succ _) future)
      · rcases List.mem_cons.mp initializing with same | old
        · exact Or.inl (by rw [same, rootOrder]; omega)
        · exact Or.inr old
    exact source.uninitializedTypes other oldCondition root resolved

#print axioms AcceptedFrame.letInitializer
end Goose.Proofs.ConstructionAcceptedExecution
