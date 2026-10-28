import Goose.Proofs.ConstructionAcceptedCallerContents

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem AcceptedFrame.afterConstruction
    {config : EvalConfig} {accepted : AcceptedModule config} {frame : ConstructionSourceFrame}
    {before after : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame before types)
    (outer : after = { before with construction := after.construction }) :
    AcceptedFrame config accepted frame after types := by
  have acts : before.nextAct ≤ after.nextAct := by rw [outer]; exact Nat.le_refl _
  have scopes : before.nextScope ≤ after.nextScope := by rw [outer]; exact Nat.le_refl _
  apply source.afterFreshActivation acts scopes
  · intro root outside
    rw [outer]
  · intro root outside
    rw [outer]
  · intro root outside
    rfl

#print axioms AcceptedFrame.afterConstruction
end Goose.Proofs.ConstructionAcceptedExecution
