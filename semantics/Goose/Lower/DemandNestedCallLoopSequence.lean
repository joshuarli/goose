import Goose.Lower.DemandWhileScalarCallAgreement

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive ReachableNestedCallLoopCursor {cfg : Cfg} {env : Env} (caller : Func) (results : List Ty) (loop : Option LoopCtx)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | existing {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : ReachableScalarCallCursor caller results loop source before built initial start map required runtime) :
      ReachableNestedCallLoopCursor caller results loop selected source before built initial start map required runtime
  | nested {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : WhileCallStatementCursor caller results selected source before built initial start map required runtime) :
      ReachableNestedCallLoopCursor caller results loop selected source before built initial start map required runtime

theorem accepted_generated_reachable_nested_call_loop_sequence {cfg : Cfg} {env : Env}
    (condition : Expr) (body : Core.Block) (origin : OriginId) (conditionForm : ControlPrefixExpression condition)
    (fragment : ∀ middle : St, ReachableScalarCallStatements cfg
      { env with scopes := (body.scope, middle.nextScope) :: env.scopes } body.stmts)
    (noValue : body.value = none) {later : List Stmt} (tail : ReachableScalarCallStatements cfg env later)
    {caller : Func} {results : List Ty} {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block) :
    ReachableSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop bindings want block
      (.while condition body origin :: later) (@ReachableNestedCallLoopCursor cfg env caller results loop root owner selected) ∧
    ReachableStoppedSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop bindings want block
      (.while condition body origin :: later) := by
  have suffix := accepted_generated_reachable_scalar_call_statements tail selected before loop bindings want block
  have mapped : ReachableSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop bindings want block later
      (@ReachableNestedCallLoopCursor cfg env caller results loop root owner selected) :=
    ReachableSequencePrefixFamily.mapCursor (cursor := @ReachableScalarCallCursor cfg env caller results loop)
      (next := @ReachableNestedCallLoopCursor cfg env caller results loop root owner selected)
      (selected := selected) (before := before) (loop := loop) (bindings := bindings) (want := want) (block := block) (statements := later)
      (fun {state} => suffix.1 (state := state)) (by
        intro statement state source before built initial start map required runtime cursor
        exact .existing cursor)
  have agreement := accepted_generated_while_scalar_call_agreement (loop := loop) selected condition body origin conditionForm fragment noValue
  have head : ReachableStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected loop (.while condition body origin)
      (@ReachableNestedCallLoopCursor cfg env caller results loop root owner selected) :=
    ReachableStatementPrefixFamily.mapCursor (cursor := @WhileCallStatementCursor cfg env caller results root owner selected)
      (next := @ReachableNestedCallLoopCursor cfg env caller results loop root owner selected)
      (selected := selected) (loop := loop) (statement := .while condition body origin)
      (fun {state} => agreement.1 (state := state)) (by
        intro statement state source before built initial start map required runtime cursor
        exact .nested cursor)
  exact ⟨accepted_generated_reachable_sequence_prefix_cons selected before loop bindings want block _ head mapped,
    accepted_generated_reachable_stopped_sequence_cons selected before loop bindings want block
      (fun {state} => agreement.2 (state := state)) (fun {state} => suffix.2 (state := state))⟩

theorem ReachableNestedCallLoopCursor.excludes_maximal_terminal {cfg : Cfg} {env : Env}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {caller : Func} {results : List Ty} {loop : Option LoopCtx} {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : ReachableNestedCallLoopCursor caller results loop selected source before built initial start map required runtime)
    {term : Term} (terminal : instAt caller runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ fuel runtime next) : False := by
  cases cursor with
  | existing cursor => exact cursor.excludes_maximal_terminal terminal maximal
  | nested cursor => exact cursor.excludes_maximal_terminal terminal maximal

#print axioms ReachableNestedCallLoopCursor.excludes_maximal_terminal

#print axioms accepted_generated_reachable_nested_call_loop_sequence
end Goose.Lower
