import Goose.Proofs.ConstructionGhostStatementCounter
import Goose.Proofs.ConstructionGhostCallHistorical

namespace Goose.Proofs.ConstructionGhostNestedActivationOrder
open Goose.Construct Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostResultScope
open Goose.Proofs.ConstructionGhostStatementCounter Goose.Proofs.ConstructionGhostCallHistorical

theorem reachedActivation_visitBeforeNestedCall {config : EvalConfig} {id : Goose.Core.ImplId}
    {activationReady boundReady : ExecutionState} {vars : Array LocalVar} {channels : List Channel}
    {pre : List (Goose.Core.VarId × Value)} {scope fuel offset : Nat} {statements : List Stmt}
    {outcome : ExecutionStep Flow} {visits : List StatementInvocation}
    (bound : let activation : RuntimeActivation := ⟨id, activationReady.nextAct, vars, [], channels⟩
      let activated := { activationReady with nextAct := activationReady.nextAct + 1, activations := activation :: activationReady.activations }
      bindAll activation.act activated.nextScope pre (resultScopeStart activation scope activated) = .ok () boundReady)
    (replay : let activation : RuntimeActivation := ⟨id, activationReady.nextAct, vars, [], channels⟩
      StatementReplay config { activation with scopes := [(scope, activationReady.nextScope)] }
        fuel offset statements boundReady outcome visits)
    (visit : StatementInvocation) (member : visit ∈ visits)
    {innerResult : ExecutionStep (List Carrier)} {innerId : Goose.Core.ActId}
    (inner : CallAllocation config visit.before innerResult innerId) : activationReady.nextAct < innerId := by
  have later := activationReplay_visitAfterAllocation
    (activation := ⟨id, activationReady.nextAct, vars, [], channels⟩)
    (before := { activationReady with nextAct := activationReady.nextAct + 1, activations := (⟨id, activationReady.nextAct, vars, [], channels⟩ : RuntimeActivation) :: activationReady.activations })
    (by simp) bound replay visit member
  have innerBounds := callAllocation_bounds inner
  exact Nat.lt_of_lt_of_le later innerBounds.1

#print axioms reachedActivation_visitBeforeNestedCall
end Goose.Proofs.ConstructionGhostNestedActivationOrder
