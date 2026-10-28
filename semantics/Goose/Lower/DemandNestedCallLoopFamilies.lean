import Goose.Lower.DemandWhileCallStoppedFamily

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem NestedCallLoopCursor.ofMixed {cfg : Cfg} {env : Env} {caller : Func} {results : List Ty}
    {root : DemandNode} {owner : Nat} {loop : Option LoopCtx} (depth : Nat)
    {selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : ReachableScalarCallCursor caller results loop source before built initial start map required runtime) :
    NestedCallLoopCursor caller results depth loop selected source before built initial start map required runtime := by
  cases depth with
  | zero => exact cursor
  | succ depth => exact .mixed cursor

theorem accepted_generated_bounded_nested_call_loop_statements {cfg : Cfg} {env : Env} {depth : Nat} {statements : List Stmt}
    (fragment : BoundedNestedCallLoopStatements cfg depth env statements) :
    ∀ {caller : Func} {results : List Ty} {root : DemandNode} {owner : Nat}
      (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
      (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block),
      ReachableSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop bindings want block statements
        (@NestedCallLoopCursor cfg caller results root owner depth env loop selected) ∧
      ReachableStoppedSequencePrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop bindings want block statements := by
  induction fragment with
  | @mixed depth env statements fragment =>
    intro caller results root owner selected before loop bindings want block
    have original := accepted_generated_reachable_scalar_call_statements fragment selected before loop bindings want block
    constructor
    · exact ReachableSequencePrefixFamily.mapCursor (cursor := @ReachableScalarCallCursor cfg env caller results loop)
        (next := @NestedCallLoopCursor cfg caller results root owner depth env loop selected)
        (selected := selected) (before := before) (loop := loop) (bindings := bindings) (want := want) (block := block) (statements := statements)
        (fun {state} => original.1 (state := state)) (by
          intro statement state source before built initial start map required runtime cursor
          exact NestedCallLoopCursor.ofMixed depth cursor)
    · exact fun {state} => original.2 (state := state)
  | @loop depth env condition body origin conditionForm bodyForm noValue later tail bodyIH tailIH =>
    intro caller results root owner selected before loop bindings want block
    have families : ∀ (middle : St) (before : LS) (innerLoop : Option LoopCtx),
        ReachableSequencePrefixFamily (env := { env with scopes := (body.scope, middle.nextScope) :: env.scopes })
          ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before innerLoop [] false body body.stmts
          (@NestedCallLoopCursor cfg caller results root owner depth { env with scopes := (body.scope, middle.nextScope) :: env.scopes } innerLoop selected) ∧
        ReachableStoppedSequencePrefixFamily (env := { env with scopes := (body.scope, middle.nextScope) :: env.scopes })
          ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before innerLoop [] false body body.stmts := by
      intro middle before innerLoop
      exact bodyIH middle selected before innerLoop [] false body
    have head : ReachableStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected loop (.while condition body origin)
        (@NestedCallLoopCursor cfg caller results root owner (depth + 1) env loop selected) :=
      ReachableStatementPrefixFamily.mapCursor
        (cursor := @NestedWhileStatementCursor cfg env caller results depth root owner selected)
        (next := @NestedCallLoopCursor cfg caller results root owner (depth + 1) env loop selected)
        (selected := selected) (loop := loop) (statement := .while condition body origin)
        (accepted_generated_while_bounded_nested_call_prefix_family selected condition body origin bodyForm noValue families
          (accepted_generated_control_progress_prefix_family selected loop conditionForm)) (by
          intro statement state source before built initial start map required runtime cursor
          exact cursor.toNested)
    have stopped : ReachableStoppedStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected loop (.while condition body origin) :=
      accepted_generated_while_bounded_nested_call_stopped_family selected condition body origin bodyForm noValue families
        (accepted_generated_read_stopped_expressions selected loop conditionForm.stopped)
    have suffix := tailIH selected before loop bindings want block
    exact ⟨accepted_generated_reachable_sequence_prefix_cons selected before loop bindings want block _ head suffix.1,
      accepted_generated_reachable_stopped_sequence_cons selected before loop bindings want block stopped suffix.2⟩

#print axioms NestedCallLoopCursor.ofMixed
#print axioms accepted_generated_bounded_nested_call_loop_statements
end Goose.Lower
