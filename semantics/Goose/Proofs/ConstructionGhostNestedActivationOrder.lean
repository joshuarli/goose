import Goose.Proofs.ConstructionGhostStatementCounter
import Goose.Proofs.ConstructionGhostCallHistorical

namespace Goose.Proofs.ConstructionGhostNestedActivationOrder
open Goose.Construct Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostResultScope
open Goose.Proofs.ConstructionGhostStatementCounter Goose.Proofs.ConstructionGhostCallHistorical
open Goose.Proofs.ConstructionActivationCounter Goose.Proofs.ConstructionAcceptedExecution Goose.Proofs.ExitExecution

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

theorem reachedActivation_visitBeforePreparedCall {config : EvalConfig} {id : Goose.Core.ImplId}
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
    (context : Goose.Core.ContextId) (lookupReady callReady : ExecutionState) (implementationId : Goose.Core.ImplId)
    (implementation : Impl) (resultChannels : List Channel) (origin : Goose.Core.OriginId)
    (lookup : getImplementation config context visit.before = .ok (implementationId, implementation) lookupReady)
    (allocated : channelsFor config.layout activationReady.nextAct implementation.results.toList origin lookupReady = .ok resultChannels callReady)
    {innerResult : ExecutionStep (List Carrier)} {innerId : Goose.Core.ActId}
    (inner : CallAllocation config callReady innerResult innerId) : activationReady.nextAct < innerId := by
  have later := activationReplay_visitAfterAllocation
    (activation := ⟨id, activationReady.nextAct, vars, [], channels⟩)
    (before := { activationReady with nextAct := activationReady.nextAct + 1, activations := (⟨id, activationReady.nextAct, vars, [], channels⟩ : RuntimeActivation) :: activationReady.activations })
    (by simp) bound replay visit member
  have lookupCounter := counter_stateQuery _ (stateQuery_getImplementation config context) visit.before
  rw [lookup] at lookupCounter
  have channelsCounter := counter_channelsFor config.layout activationReady.nextAct implementation.results.toList origin lookupReady
  rw [allocated] at channelsCounter
  have innerBounds := callAllocation_bounds inner
  simp only [Goose.Proofs.Exit.stepState] at lookupCounter channelsCounter
  exact Nat.lt_of_lt_of_le later (Nat.le_trans lookupCounter (Nat.le_trans channelsCounter innerBounds.1))

#print axioms reachedActivation_visitBeforePreparedCall
#print axioms reachedActivation_visitBeforeNestedCall
end Goose.Proofs.ConstructionGhostNestedActivationOrder
