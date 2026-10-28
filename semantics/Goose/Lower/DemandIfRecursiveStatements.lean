import Goose.Lower.DemandIfRecursiveThenStopped

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_bounded_if_statements {cfg : Cfg} {depth : Nat} {env : Env} {statements : List Stmt}
    (fragment : BoundedIfStatements cfg depth env statements) :
    ∀ {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
      (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
      (before : LS) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block),
      GeneratedSequencePrefixFamily cx results selected before none bindings want block statements
          (@RecursiveIfCursor cfg cx results root owner depth env selected) ∧
        GeneratedStoppedSequencePrefixFamily cx results selected before none bindings want block statements := by
  induction fragment with
  | nil depth env =>
    intro cx results root owner selected before bindings want block
    exact ⟨fun {state} => accepted_generated_sequence_prefix_nil selected before none bindings want block _,
      fun {state} => accepted_generated_stopped_sequence_nil selected before none bindings want block⟩
  | @scalar depth env segment rest fragment tail ih =>
    intro cx results root owner selected before bindings want block
    apply accepted_generated_scalar_assignment_statements_prepend selected before none bindings want block fragment _ ?_
      (ih selected before bindings want block)
    intro statement state source before built initial start map required runtime cursor
    cases depth with
    | zero => exact cursor
    | succ depth => exact .scalar cursor
  | @conditional depth env condition form yes origin branch noValue rest tail branchIH tailIH =>
    intro cx results root owner selected before bindings want block
    have branchFamily : RecursiveIfBranchFamily cx results selected depth yes := by
      intro state before
      exact branchIH state selected before [] false yes
    have head : GeneratedStatementPrefixFamily cx results selected none (.ifS condition yes none origin)
        (@RecursiveIfCursor cfg cx results root owner (depth + 1) env selected) :=
      accepted_generated_recursive_if_none_prefix_family selected depth condition yes origin branch branchFamily noValue
      (accepted_generated_control_progress_prefix_family selected none form)
    have stop : GeneratedStoppedStatementPrefixFamily cx results selected none (.ifS condition yes none origin) :=
      accepted_generated_recursive_if_none_stopped_family selected depth condition yes origin branch branchFamily noValue
      (accepted_generated_read_stopped_expressions selected none form.stopped)
    exact ⟨fun {state} => accepted_generated_sequence_prefix_cons selected before none bindings want block _ head
        (tailIH selected before bindings want block).1,
      fun {state} => accepted_generated_stopped_sequence_cons selected before none bindings want block stop
        (tailIH selected before bindings want block).2⟩
  | @conditionalElse depth env condition form yes no origin yesBranch noBranch yesNoValue noNoValue rest tail yesIH noIH tailIH =>
    intro cx results root owner selected before bindings want block
    have yesFamily : RecursiveIfBranchFamily cx results selected depth yes := by
      intro state before
      exact yesIH state selected before [] false yes
    have noFamily : RecursiveIfBranchFamily cx results selected depth no := by
      intro state before
      exact noIH state selected before [] false no
    have head : GeneratedStatementPrefixFamily cx results selected none (.ifS condition yes (some no) origin)
        (@RecursiveIfCursor cfg cx results root owner (depth + 1) env selected) :=
      accepted_generated_recursive_if_some_prefix_family selected depth condition yes no origin yesBranch noBranch
      yesFamily noFamily yesNoValue noNoValue (accepted_generated_control_progress_prefix_family selected none form)
    have stop : GeneratedStoppedStatementPrefixFamily cx results selected none (.ifS condition yes (some no) origin) :=
      accepted_generated_recursive_if_some_stopped_family selected depth condition yes no origin yesBranch noBranch
      yesFamily noFamily yesNoValue noNoValue (accepted_generated_read_stopped_expressions selected none form.stopped)
    exact ⟨fun {state} => accepted_generated_sequence_prefix_cons selected before none bindings want block _ head
        (tailIH selected before bindings want block).1,
      fun {state} => accepted_generated_stopped_sequence_cons selected before none bindings want block stop
        (tailIH selected before bindings want block).2⟩

theorem accepted_generated_recursive_if_statements {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (block : Core.Block) {statements : List Stmt} (fragment : RecursiveIfStatements cfg env statements) :
    GeneratedSequencePrefixFamily cx results selected before none bindings want block statements
        (@RecursiveIfCursor cfg cx results root owner (Place._sizeOf_11 statements) env selected) ∧
      GeneratedStoppedSequencePrefixFamily cx results selected before none bindings want block statements :=
  accepted_generated_bounded_if_statements fragment.bounded selected before bindings want block

#print axioms accepted_generated_recursive_if_statements
#print axioms accepted_generated_bounded_if_statements
end Goose.Lower
