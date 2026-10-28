import Goose.Proofs.ConstructionAcceptedNestedScope
import Goose.Proofs.ConstructionAcceptedGlobalPrefix

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem AcceptedFrame.restoreEmptyVariables {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {before after : ExecutionState} {types nextTypes : RootTypes}
    (source : AcceptedFrame config accepted frame before types)
    (empty : frame.interpretation.environment.vars = #[])
    (acts : before.nextAct ≤ after.nextAct) (scopes : before.nextScope ≤ after.nextScope)
    (clear : FutureGlobalsClear config frame.initialized after) :
    AcceptedFrame config accepted frame after nextTypes := by
  have emptyTypes : frame.typing.variables = #[] := source.compatible.variables.symm.trans empty
  have noVisible : frame.typing.visible = [] := by
    have zeroCounter : frame.typingCounter = 0 := by
      have bound := source.compatible.typingBound
      simp only [emptyTypes, Array.size_empty] at bound
      omega
    have zeroRoots : frame.rootCursor.nextVar = 0 := by
      have bound := source.compatible.declarations
      omega
    cases visible : frame.typing.visible with
    | nil => rfl
    | cons id rest =>
      have bound := source.compatible.visible id (by simp [visible])
      rw [zeroRoots] at bound
      exact (Nat.not_lt_zero id bound).elim
  refine ⟨source.compatible, rootFrontier_mono source.frontier acts, ?_, source.initializingBefore, source.aliases,
    ?_, ?_, ?_, ?_, clear, ?_, ?_⟩
  · intro entry member
    exact Nat.lt_of_lt_of_le (source.scopeFrontier entry member) scopes
  · simp [LocalRepresentations, noVisible]
  · simp [noVisible]
  · intro id condition root resolved
    simp [rootOf, empty, fault, EvalM.stop] at resolved
  · intro id condition root resolved
    simp [rootOf, empty, fault, EvalM.stop] at resolved
  · simp [LocalRootCorrespondence, noVisible]
  · simp [ContentRootCorrespondence, noVisible]

#print axioms AcceptedFrame.restoreEmptyVariables
end Goose.Proofs.ConstructionAcceptedExecution
