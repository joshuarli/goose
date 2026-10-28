import Goose.Lower.DemandIfMixedSequence

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive IfMixedStatements (cfg : Cfg) (env : Env) : List Stmt → Prop
  | nil : IfMixedStatements cfg env []
  | scalar {segment rest : List Stmt} (fragment : ScalarAssignmentStatements cfg env segment)
      (tail : IfMixedStatements cfg env rest) : IfMixedStatements cfg env (segment ++ rest)
  | conditional {condition : Expr} (form : ControlPrefixExpression condition) (yes : Core.Block) (origin : OriginId)
      (branch : ∀ state : St, ScalarAssignmentStatements cfg
        { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
      (noValue : yes.value = none) {rest : List Stmt} (tail : IfMixedStatements cfg env rest) :
      IfMixedStatements cfg env (.ifS condition yes none origin :: rest)
  | conditionalElse {condition : Expr} (form : ControlPrefixExpression condition) (yes no : Core.Block) (origin : OriginId)
      (yesBranch : ∀ state : St, ScalarAssignmentStatements cfg
        { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
      (noBranch : ∀ state : St, ScalarAssignmentStatements cfg
        { env with scopes := (no.scope, state.nextScope) :: env.scopes } no.stmts)
      (yesNoValue : yes.value = none) (noNoValue : no.value = none) {rest : List Stmt} (tail : IfMixedStatements cfg env rest) :
      IfMixedStatements cfg env (.ifS condition yes (some no) origin :: rest)

theorem accepted_generated_if_mixed_statements {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (block : Core.Block) {statements : List Stmt} (fragment : IfMixedStatements cfg env statements) :
    GeneratedSequencePrefixFamily cx results selected before none bindings want block statements
        (@IfMixedStatementCursor cfg env cx results root owner selected) ∧
      GeneratedStoppedSequencePrefixFamily cx results selected before none bindings want block statements := by
  induction fragment with
  | nil =>
    exact ⟨fun {state} => accepted_generated_sequence_prefix_nil selected before none bindings want block _,
      fun {state} => accepted_generated_stopped_sequence_nil selected before none bindings want block⟩
  | scalar fragment tail ih =>
    apply accepted_generated_scalar_assignment_statements_prepend selected before none bindings want block fragment _ ?_ ih
    intro statement state source before built initial start map required runtime cursor
    exact .scalar cursor
  | @conditional condition form yes origin branch noValue rest tail ih =>
    have head : GeneratedStatementPrefixFamily cx results selected none (.ifS condition yes none origin)
        (@IfStatementPrefixCursor cfg env cx results root owner selected) :=
      accepted_generated_if_none_prefix_family selected condition yes origin branch noValue
        (accepted_generated_control_prefix_family selected none form)
    have mapped : GeneratedStatementPrefixFamily cx results selected none (.ifS condition yes none origin)
        (@IfMixedStatementCursor cfg env cx results root owner selected) := by
      apply GeneratedStatementPrefixFamily.mapCursor head
      intro statement state source before built initial start map required runtime cursor
      exact .conditional cursor
    exact ⟨fun {state} => accepted_generated_sequence_prefix_cons selected before none bindings want block _ mapped ih.1,
      fun {state} => accepted_generated_stopped_sequence_cons selected before none bindings want block
        (accepted_generated_if_none_stopped_family selected condition yes origin branch noValue
          (accepted_generated_read_stopped_expressions selected none form.stopped)) ih.2⟩
  | @conditionalElse condition form yes no origin yesBranch noBranch yesNoValue noNoValue rest tail ih =>
    have head : GeneratedStatementPrefixFamily cx results selected none (.ifS condition yes (some no) origin)
        (@IfElseStatementPrefixCursor cfg env cx results root owner selected) :=
      accepted_generated_if_some_prefix_family selected condition yes no origin yesBranch noBranch yesNoValue noNoValue
        (accepted_generated_control_prefix_family selected none form)
    have mapped : GeneratedStatementPrefixFamily cx results selected none (.ifS condition yes (some no) origin)
        (@IfMixedStatementCursor cfg env cx results root owner selected) := by
      apply GeneratedStatementPrefixFamily.mapCursor head
      intro statement state source before built initial start map required runtime cursor
      exact .conditionalElse cursor
    exact ⟨fun {state} => accepted_generated_sequence_prefix_cons selected before none bindings want block _ mapped ih.1,
      fun {state} => accepted_generated_stopped_sequence_cons selected before none bindings want block
        (accepted_generated_if_some_stopped_family selected condition yes no origin yesBranch noBranch yesNoValue noNoValue
          (accepted_generated_read_stopped_expressions selected none form.stopped)) ih.2⟩

#print axioms accepted_generated_if_mixed_statements
#print axioms accepted_generated_scalar_assignment_statements_prepend
end Goose.Lower
