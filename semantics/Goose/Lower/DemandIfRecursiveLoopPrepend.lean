import Goose.Lower.DemandWhileMixedStatements
import Goose.Lower.DemandIfRecursiveLoopStatements

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive LoopRecursiveSegmentCursor {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty) (loop : Option LoopCtx)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | scalar {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : ScalarAssignmentStatementPrefixCursor cx results source before built initial start map required runtime) :
      LoopRecursiveSegmentCursor cx results loop selected source before built initial start map required runtime
  | recursive {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (depth : Nat) (cursor : RecursiveLoopIfCursor cx results loop depth selected source before built initial start map required runtime) :
      LoopRecursiveSegmentCursor cx results loop selected source before built initial start map required runtime

theorem accepted_generated_invariant_recursive_loop_if_prepend {cfg : Cfg} {env : Env} {statements : List Stmt}
    (fragment : RecursiveIfStatements cfg env statements) :
    ∀ {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
      (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
      (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block)
      (cursor : ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
        LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
      (convert : ∀ {statement : Stmt} {state : St} (source : StmtSource cfg env statement state)
        {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
        LoopRecursiveSegmentCursor cx results loop selected source before built initial start map required runtime →
          cursor source before built initial start map required runtime)
      (invariant : DemandRuntimePoint → Prop)
      (advance : ∀ {length : Nat} {first last : DemandRuntimePoint}, invariant first → DemandRuntimePrefix cx length first last → invariant last)
      {rest : List Stmt},
      (InvariantSequencePrefixFamily cx results selected before loop bindings want block rest
        (@cursor) invariant ∧
       InvariantStoppedSequencePrefixFamily cx results selected before loop bindings want block rest invariant) →
      InvariantSequencePrefixFamily cx results selected before loop bindings want block (statements ++ rest)
        (@cursor) invariant ∧
      InvariantStoppedSequencePrefixFamily cx results selected before loop bindings want block (statements ++ rest) invariant := by
  induction fragment with
  | nil env =>
    intro cx results root owner selected before loop bindings want block cursor convert invariant advance rest tail
    simpa using tail
  | @scalar env segment statements scalar tail ih =>
    intro cx results root owner selected before loop bindings want block cursor convert invariant advance rest restFamily
    simpa only [List.append_assoc] using
      (accepted_generated_invariant_scalar_assignment_statements_prepend selected before loop bindings want block scalar cursor
        (by
          intro statement state source before built initial start map required runtime cursor
          exact convert source (.scalar cursor))
        invariant advance (ih selected before loop bindings want block cursor convert invariant advance restFamily))
  | @conditional env condition form yes origin branch noValue statements tail branchIH tailIH =>
    intro cx results root owner selected before loop bindings want block cursor convert invariant advance rest restFamily
    let depth := Place._sizeOf_11 yes.stmts
    have bounded : ∀ state : St, BoundedIfStatements cfg depth
        { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts := fun state => (branch state).bounded
    have branchFamily : RecursiveLoopIfBranchFamily cx results selected loop depth yes := by
      intro state branchBefore
      exact accepted_generated_bounded_loop_if_statements loop (bounded state) selected branchBefore [] false yes
    have head : GeneratedStatementPrefixFamily cx results selected loop (.ifS condition yes none origin)
        (@LoopRecursiveSegmentCursor cfg env cx results loop root owner selected) := by
      apply GeneratedStatementPrefixFamily.mapCursor
        (accepted_generated_recursive_loop_if_none_prefix_family loop selected depth condition yes origin bounded branchFamily noValue
          (accepted_generated_control_progress_prefix_family selected loop form))
      intro statement state source before built initial start map required runtime cursor
      exact .recursive (depth + 1) cursor
    have stopped : GeneratedStoppedStatementPrefixFamily cx results selected loop (.ifS condition yes none origin) :=
      accepted_generated_recursive_loop_if_none_stopped_family loop selected depth condition yes origin bounded branchFamily noValue
      (accepted_generated_read_stopped_expressions selected loop form.stopped)
    have next : InvariantSequencePrefixFamily cx results selected before loop bindings want block (statements ++ rest)
          (@cursor) invariant ∧
        InvariantStoppedSequencePrefixFamily cx results selected before loop bindings want block (statements ++ rest) invariant :=
      tailIH selected before loop bindings want block cursor convert invariant advance restFamily
    exact ⟨fun {state} => accepted_generated_invariant_sequence_prefix_cons selected before loop bindings want block cursor invariant advance
        (GeneratedStatementPrefixFamily.withInvariant (GeneratedStatementPrefixFamily.mapCursor head convert) invariant) next.1,
      fun {state} => accepted_generated_invariant_stopped_sequence_cons selected before loop bindings want block invariant advance
        (GeneratedStoppedStatementPrefixFamily.withInvariant stopped invariant) next.2⟩
  | @conditionalElse env condition form yes no origin yesBranch noBranch yesNoValue noNoValue statements tail yesIH noIH tailIH =>
    intro cx results root owner selected before loop bindings want block cursor convert invariant advance rest restFamily
    let depth := max (Place._sizeOf_11 yes.stmts) (Place._sizeOf_11 no.stmts)
    have yesBounded : ∀ state : St, BoundedIfStatements cfg depth
        { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts :=
      fun state => (yesBranch state).bounded.mono (Nat.le_max_left _ _)
    have noBounded : ∀ state : St, BoundedIfStatements cfg depth
        { env with scopes := (no.scope, state.nextScope) :: env.scopes } no.stmts :=
      fun state => (noBranch state).bounded.mono (Nat.le_max_right _ _)
    have yesFamily : RecursiveLoopIfBranchFamily cx results selected loop depth yes := by
      intro state branchBefore
      exact accepted_generated_bounded_loop_if_statements loop (yesBounded state) selected branchBefore [] false yes
    have noFamily : RecursiveLoopIfBranchFamily cx results selected loop depth no := by
      intro state branchBefore
      exact accepted_generated_bounded_loop_if_statements loop (noBounded state) selected branchBefore [] false no
    have head : GeneratedStatementPrefixFamily cx results selected loop (.ifS condition yes (some no) origin)
        (@LoopRecursiveSegmentCursor cfg env cx results loop root owner selected) := by
      apply GeneratedStatementPrefixFamily.mapCursor
        (accepted_generated_recursive_loop_if_some_prefix_family loop selected depth condition yes no origin yesBounded noBounded
          yesFamily noFamily yesNoValue noNoValue (accepted_generated_control_progress_prefix_family selected loop form))
      intro statement state source before built initial start map required runtime cursor
      exact .recursive (depth + 1) cursor
    have stopped : GeneratedStoppedStatementPrefixFamily cx results selected loop (.ifS condition yes (some no) origin) :=
      accepted_generated_recursive_loop_if_some_stopped_family loop selected depth condition yes no origin yesBounded noBounded
      yesFamily noFamily yesNoValue noNoValue (accepted_generated_read_stopped_expressions selected loop form.stopped)
    have next : InvariantSequencePrefixFamily cx results selected before loop bindings want block (statements ++ rest)
          (@cursor) invariant ∧
        InvariantStoppedSequencePrefixFamily cx results selected before loop bindings want block (statements ++ rest) invariant :=
      tailIH selected before loop bindings want block cursor convert invariant advance restFamily
    exact ⟨fun {state} => accepted_generated_invariant_sequence_prefix_cons selected before loop bindings want block cursor invariant advance
        (GeneratedStatementPrefixFamily.withInvariant (GeneratedStatementPrefixFamily.mapCursor head convert) invariant) next.1,
      fun {state} => accepted_generated_invariant_stopped_sequence_cons selected before loop bindings want block invariant advance
        (GeneratedStoppedStatementPrefixFamily.withInvariant stopped invariant) next.2⟩


#print axioms accepted_generated_invariant_recursive_loop_if_prepend
end Goose.Lower
