import Goose.Lower.DemandIfPrefixFamily

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem GeneratedSequencePrefixCursor.map {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {cursor next : ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop}
    (convert : ∀ {statement : Stmt} {state : St} (source : StmtSource cfg env statement state)
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
      cursor source before built initial start map required runtime → next source before built initial start map required runtime)
    {map required : RetainedSsaMap} {before : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {block : Core.Block}
    {statements : List Stmt} {state : St} {source : StmtsSource cfg env statements state}
    {start reached : DemandRuntimePoint}
    (demanded : GeneratedSequencePrefixCursor cursor map required cx results before loop bindings block selected source start reached) :
    GeneratedSequencePrefixCursor next map required cx results before loop bindings block selected source start reached := by
  induction demanded with
  | head canonical owned occurrence rows coverage demanded =>
    exact .head canonical owned occurrence rows coverage (convert _ demanded)
  | tail canonical evaluated prefixSteps post demanded induction =>
    exact .tail canonical evaluated prefixSteps post induction

theorem GeneratedSequencePrefixFamily.mapCursor {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {before : LS} {loop : Option LoopCtx} {bindings : List (SlotId × ValueId × OriginId)} {want : Bool}
    {block : Core.Block} {statements : List Stmt}
    {cursor next : ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop}
    (family : GeneratedSequencePrefixFamily cx results selected before loop bindings want block statements cursor)
    (convert : ∀ {statement : Stmt} {state : St} (source : StmtSource cfg env statement state)
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
      cursor source before built initial start map required runtime → next source before built initial start map required runtime) :
    GeneratedSequencePrefixFamily cx results selected before loop bindings want block statements next := by
  intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended taken reached steps
  have decomposition := family source owned occurrence all scope value rows coverage admitted bounded realized input extended steps
  refine ⟨decomposition.sourceOwner, decomposition.coverage, ?_⟩
  cases decomposition.progress with
  | interior demanded => exact .interior (demanded.map convert)
  | complete count prefixSteps residual evaluated post => exact .complete count prefixSteps residual evaluated post

inductive IfMixedStatementCursor {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | scalar {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : ScalarAssignmentStatementPrefixCursor cx results source before built initial start map required runtime) :
      IfMixedStatementCursor cx results selected source before built initial start map required runtime
  | conditional {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : IfStatementPrefixCursor cx results selected source before built initial start map required runtime) :
      IfMixedStatementCursor cx results selected source before built initial start map required runtime

theorem accepted_generated_if_mixed_sequence {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block)
    (condition : Expr) (yes : Core.Block) (origin : OriginId) {rest : List Stmt}
    (fragment : ∀ state : St, ScalarAssignmentStatements cfg
      { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
    (noValue : yes.value = none) (tail : ScalarAssignmentStatements cfg env rest)
    (conditionFamily : GeneratedExpressionPrefixFamily cx results selected none condition (@CanonicalExpressionPrefixCursor cfg env cx))
    (conditionStopped : GeneratedStoppedExpressionPrefixFamily cx results selected none condition) :
    GeneratedSequencePrefixFamily cx results selected before none bindings want block (.ifS condition yes none origin :: rest)
        (@IfMixedStatementCursor cfg env cx results root owner selected) ∧
      GeneratedStoppedSequencePrefixFamily cx results selected before none bindings want block (.ifS condition yes none origin :: rest) := by
  have tailFamily := accepted_generated_scalar_assignment_statements_agreement selected before none bindings want block tail
  have mappedTail : GeneratedSequencePrefixFamily cx results selected before none bindings want block rest
      (@IfMixedStatementCursor cfg env cx results root owner selected) := by
    apply GeneratedSequencePrefixFamily.mapCursor tailFamily.1
    intro statement state source before built initial start map required runtime cursor
    exact .scalar cursor
  have head : GeneratedStatementPrefixFamily cx results selected none (.ifS condition yes none origin)
      (@IfMixedStatementCursor cfg env cx results root owner selected) := by
    apply GeneratedStatementPrefixFamily.mapCursor
      (accepted_generated_if_none_prefix_family selected condition yes origin fragment noValue conditionFamily)
    intro statement state source before built initial start map required runtime cursor
    exact .conditional cursor
  exact ⟨accepted_generated_sequence_prefix_cons selected before none bindings want block _ head mappedTail,
    accepted_generated_stopped_sequence_cons selected before none bindings want block
      (accepted_generated_if_none_stopped_family selected condition yes origin fragment noValue conditionStopped) tailFamily.2⟩

#print axioms accepted_generated_if_mixed_sequence
end Goose.Lower
