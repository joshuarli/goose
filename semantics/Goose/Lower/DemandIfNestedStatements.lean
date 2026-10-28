import Goose.Lower.DemandIfNestedPrefixFamily

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive NestedIfMixedStatements (cfg : Cfg) (env : Env) : List Stmt → Prop
  | nil : NestedIfMixedStatements cfg env []
  | scalar {segment rest : List Stmt} (fragment : ScalarAssignmentStatements cfg env segment)
      (tail : NestedIfMixedStatements cfg env rest) : NestedIfMixedStatements cfg env (segment ++ rest)
  | conditionalElse {condition : Expr} (form : ControlPrefixExpression condition) (yes no : Core.Block) (origin : OriginId)
      (yesBranch : ∀ state : St, IfMixedStatements cfg
        { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
      (noBranch : ∀ state : St, IfMixedStatements cfg
        { env with scopes := (no.scope, state.nextScope) :: env.scopes } no.stmts)
      (yesNoValue : yes.value = none) (noNoValue : no.value = none) {rest : List Stmt} (tail : NestedIfMixedStatements cfg env rest) :
      NestedIfMixedStatements cfg env (.ifS condition yes (some no) origin :: rest)

inductive NestedIfMixedStatementCursor {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | scalar {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : ScalarAssignmentStatementPrefixCursor cx results source before built initial start map required runtime) :
      NestedIfMixedStatementCursor cx results selected source before built initial start map required runtime
  | conditionalElse {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : NestedIfElseStatementPrefixCursor cx results selected source before built initial start map required runtime) :
      NestedIfMixedStatementCursor cx results selected source before built initial start map required runtime

theorem NestedIfMixedStatements.fragment {cfg : Cfg} {env : Env} {statements : List Stmt}
    (form : NestedIfMixedStatements cfg env statements) : stmtsOk statements = true := by
  induction form with
  | nil => rfl
  | scalar fragment tail ih => exact stmtsOk_append fragment.fragment ih
  | conditionalElse condition yes no origin yesBranch noBranch yesNoValue noNoValue tail ih =>
    have yesValid := (yesBranch St.initial).fragment
    have noValid := (noBranch St.initial).fragment
    cases yes with
    | mk yesScope yesStatements yesValue =>
      cases no with
      | mk noScope noStatements noValue =>
        simp only [Core.Block.value] at yesNoValue noNoValue
        subst yesValue
        subst noValue
        simp only [Core.Block.stmts] at yesValid noValid
        simp [stmtsOk, stmtOk, blockOk, condition.fragment, yesValid, noValid, ih]

theorem NestedIfMixedStatements.normal {cfg : Cfg} {env : Env} {statements : List Stmt}
    (form : NestedIfMixedStatements cfg env statements) {fuel : Nat} {state after : St} {flow : Flow}
    (done : execStmts fuel cfg env statements state = .ok flow after) : flow = .normal .unit :=
  stmts_fragment_normal form.fragment done

theorem accepted_generated_nested_if_mixed_statements {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (block : Core.Block) {statements : List Stmt} (fragment : NestedIfMixedStatements cfg env statements) :
    GeneratedSequencePrefixFamily cx results selected before none bindings want block statements
        (@NestedIfMixedStatementCursor cfg env cx results root owner selected) ∧
      GeneratedStoppedSequencePrefixFamily cx results selected before none bindings want block statements := by
  induction fragment with
  | nil =>
    exact ⟨fun {state} => accepted_generated_sequence_prefix_nil selected before none bindings want block _,
      fun {state} => accepted_generated_stopped_sequence_nil selected before none bindings want block⟩
  | scalar fragment tail ih =>
    apply accepted_generated_scalar_assignment_statements_prepend selected before none bindings want block fragment _ ?_ ih
    intro statement state source before built initial start map required runtime cursor
    exact .scalar cursor
  | @conditionalElse condition form yes no origin yesBranch noBranch yesNoValue noNoValue rest tail ih =>
    have head : GeneratedStatementPrefixFamily cx results selected none (.ifS condition yes (some no) origin)
        (@NestedIfElseStatementPrefixCursor cfg env cx results root owner selected) :=
      accepted_generated_nested_if_some_prefix_family selected condition yes no origin yesBranch noBranch yesNoValue noNoValue
        (accepted_generated_control_prefix_family selected none form)
    have mapped : GeneratedStatementPrefixFamily cx results selected none (.ifS condition yes (some no) origin)
        (@NestedIfMixedStatementCursor cfg env cx results root owner selected) := by
      apply GeneratedStatementPrefixFamily.mapCursor head
      intro statement state source before built initial start map required runtime cursor
      exact .conditionalElse cursor
    exact ⟨fun {state} => accepted_generated_sequence_prefix_cons selected before none bindings want block _ mapped ih.1,
      fun {state} => accepted_generated_stopped_sequence_cons selected before none bindings want block
        (accepted_generated_nested_if_some_stopped_family selected condition yes no origin yesBranch noBranch yesNoValue noNoValue
          (accepted_generated_read_stopped_expressions selected none form.stopped)) ih.2⟩

#print axioms NestedIfMixedStatements.normal
#print axioms accepted_generated_nested_if_mixed_statements
end Goose.Lower
