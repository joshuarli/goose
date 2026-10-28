import Goose.Lower.DemandWhileAgreement

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive WhileMixedStatements (cfg : Cfg) (env : Env) : List Stmt → Prop
  | nil : WhileMixedStatements cfg env []
  | scalar {segment rest : List Stmt} (fragment : ScalarAssignmentStatements cfg env segment)
      (tail : WhileMixedStatements cfg env rest) : WhileMixedStatements cfg env (segment ++ rest)
  | recursive {segment rest : List Stmt} (fragment : RecursiveIfStatements cfg env segment)
      (tail : WhileMixedStatements cfg env rest) : WhileMixedStatements cfg env (segment ++ rest)
  | loop (condition : Expr) (body : Core.Block) (origin : OriginId) (form : ControlPrefixExpression condition)
      (fragment : ∀ middle : St, RecursiveIfStatements cfg
        { env with scopes := (body.scope, middle.nextScope) :: env.scopes } body.stmts)
      (noValue : body.value = none) {rest : List Stmt} (tail : WhileMixedStatements cfg env rest) :
      WhileMixedStatements cfg env (.while condition body origin :: rest)

inductive WhileMixedStatementCursor {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty)
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | scalar {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : ScalarAssignmentStatementPrefixCursor cx results source before built initial start map required runtime) :
      WhileMixedStatementCursor cx results selected source before built initial start map required runtime
  | recursive {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (depth : Nat) (cursor : RecursiveIfCursor cx results depth selected source before built initial start map required runtime) :
      WhileMixedStatementCursor cx results selected source before built initial start map required runtime
  | loop {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : WhileStatementPrefixCursor cx results selected source before built initial start map required runtime) :
      WhileMixedStatementCursor cx results selected source before built initial start map required runtime

theorem WhileMixedStatements.fragment {cfg : Cfg} {env : Env} {statements : List Stmt}
    (form : WhileMixedStatements cfg env statements) : stmtsOk statements = true := by
  induction form with
  | nil => rfl
  | scalar fragment tail ih => exact stmtsOk_append fragment.fragment ih
  | recursive fragment tail ih => exact stmtsOk_append fragment.fragment ih
  | loop condition body origin form fragment noValue tail ih =>
    have valid := (fragment St.initial).fragment
    cases body with
    | mk scope statements value =>
      simp only [Core.Block.value] at noValue
      subst value
      simp only [Core.Block.stmts] at valid
      simp [stmtsOk, stmtOk, blockOk, form.fragment, valid, ih]

theorem WhileMixedStatements.normal {cfg : Cfg} {env : Env} {statements : List Stmt}
    (form : WhileMixedStatements cfg env statements) {fuel : Nat} {state after : St} {flow : Flow}
    (done : execStmts fuel cfg env statements state = .ok flow after) : flow = .normal .unit :=
  stmts_fragment_normal form.fragment done

theorem accepted_generated_invariant_recursive_if_statements_prepend {cfg : Cfg} {env : Env} {statements : List Stmt}
    (fragment : RecursiveIfStatements cfg env statements) :
    ∀ {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
      (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
      (before : LS) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block)
      (cursor : ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
        LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
      (convert : ∀ {statement : Stmt} {state : St} (source : StmtSource cfg env statement state)
        {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
        WhileMixedStatementCursor cx results selected source before built initial start map required runtime →
          cursor source before built initial start map required runtime)
      (invariant : DemandRuntimePoint → Prop)
      (advance : ∀ {length : Nat} {first last : DemandRuntimePoint}, invariant first → DemandRuntimePrefix cx length first last → invariant last)
      {rest : List Stmt},
      (InvariantSequencePrefixFamily cx results selected before none bindings want block rest
        (@cursor) invariant ∧
       InvariantStoppedSequencePrefixFamily cx results selected before none bindings want block rest invariant) →
      InvariantSequencePrefixFamily cx results selected before none bindings want block (statements ++ rest)
        (@cursor) invariant ∧
      InvariantStoppedSequencePrefixFamily cx results selected before none bindings want block (statements ++ rest) invariant := by
  induction fragment with
  | nil env =>
    intro cx results root owner selected before bindings want block cursor convert invariant advance rest tail
    simpa using tail
  | @scalar env segment statements scalar tail ih =>
    intro cx results root owner selected before bindings want block cursor convert invariant advance rest restFamily
    simpa only [List.append_assoc] using
      (accepted_generated_invariant_scalar_assignment_statements_prepend selected before none bindings want block scalar cursor
        (by
          intro statement state source before built initial start map required runtime cursor
          exact convert source (.scalar cursor))
        invariant advance (ih selected before bindings want block cursor convert invariant advance restFamily))
  | @conditional env condition form yes origin branch noValue statements tail branchIH tailIH =>
    intro cx results root owner selected before bindings want block cursor convert invariant advance rest restFamily
    let depth := Place._sizeOf_11 yes.stmts
    have bounded : ∀ state : St, BoundedIfStatements cfg depth
        { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts := fun state => (branch state).bounded
    have branchFamily : RecursiveIfBranchFamily cx results selected depth yes := by
      intro state branchBefore
      exact accepted_generated_bounded_if_statements (bounded state) selected branchBefore [] false yes
    have head : GeneratedStatementPrefixFamily cx results selected none (.ifS condition yes none origin)
        (@WhileMixedStatementCursor cfg env cx results root owner selected) := by
      apply GeneratedStatementPrefixFamily.mapCursor
        (accepted_generated_recursive_if_none_prefix_family selected depth condition yes origin bounded branchFamily noValue
          (accepted_generated_control_progress_prefix_family selected none form))
      intro statement state source before built initial start map required runtime cursor
      exact .recursive (depth + 1) cursor
    have stopped : GeneratedStoppedStatementPrefixFamily cx results selected none (.ifS condition yes none origin) :=
      accepted_generated_recursive_if_none_stopped_family selected depth condition yes origin bounded branchFamily noValue
      (accepted_generated_read_stopped_expressions selected none form.stopped)
    have next : InvariantSequencePrefixFamily cx results selected before none bindings want block (statements ++ rest)
          (@cursor) invariant ∧
        InvariantStoppedSequencePrefixFamily cx results selected before none bindings want block (statements ++ rest) invariant :=
      tailIH selected before bindings want block cursor convert invariant advance restFamily
    exact ⟨fun {state} => accepted_generated_invariant_sequence_prefix_cons selected before none bindings want block cursor invariant advance
        (GeneratedStatementPrefixFamily.withInvariant (GeneratedStatementPrefixFamily.mapCursor head convert) invariant) next.1,
      fun {state} => accepted_generated_invariant_stopped_sequence_cons selected before none bindings want block invariant advance
        (GeneratedStoppedStatementPrefixFamily.withInvariant stopped invariant) next.2⟩
  | @conditionalElse env condition form yes no origin yesBranch noBranch yesNoValue noNoValue statements tail yesIH noIH tailIH =>
    intro cx results root owner selected before bindings want block cursor convert invariant advance rest restFamily
    let depth := max (Place._sizeOf_11 yes.stmts) (Place._sizeOf_11 no.stmts)
    have yesBounded : ∀ state : St, BoundedIfStatements cfg depth
        { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts :=
      fun state => (yesBranch state).bounded.mono (Nat.le_max_left _ _)
    have noBounded : ∀ state : St, BoundedIfStatements cfg depth
        { env with scopes := (no.scope, state.nextScope) :: env.scopes } no.stmts :=
      fun state => (noBranch state).bounded.mono (Nat.le_max_right _ _)
    have yesFamily : RecursiveIfBranchFamily cx results selected depth yes := by
      intro state branchBefore
      exact accepted_generated_bounded_if_statements (yesBounded state) selected branchBefore [] false yes
    have noFamily : RecursiveIfBranchFamily cx results selected depth no := by
      intro state branchBefore
      exact accepted_generated_bounded_if_statements (noBounded state) selected branchBefore [] false no
    have head : GeneratedStatementPrefixFamily cx results selected none (.ifS condition yes (some no) origin)
        (@WhileMixedStatementCursor cfg env cx results root owner selected) := by
      apply GeneratedStatementPrefixFamily.mapCursor
        (accepted_generated_recursive_if_some_prefix_family selected depth condition yes no origin yesBounded noBounded
          yesFamily noFamily yesNoValue noNoValue (accepted_generated_control_progress_prefix_family selected none form))
      intro statement state source before built initial start map required runtime cursor
      exact .recursive (depth + 1) cursor
    have stopped : GeneratedStoppedStatementPrefixFamily cx results selected none (.ifS condition yes (some no) origin) :=
      accepted_generated_recursive_if_some_stopped_family selected depth condition yes no origin yesBounded noBounded
      yesFamily noFamily yesNoValue noNoValue (accepted_generated_read_stopped_expressions selected none form.stopped)
    have next : InvariantSequencePrefixFamily cx results selected before none bindings want block (statements ++ rest)
          (@cursor) invariant ∧
        InvariantStoppedSequencePrefixFamily cx results selected before none bindings want block (statements ++ rest) invariant :=
      tailIH selected before bindings want block cursor convert invariant advance restFamily
    exact ⟨fun {state} => accepted_generated_invariant_sequence_prefix_cons selected before none bindings want block cursor invariant advance
        (GeneratedStatementPrefixFamily.withInvariant (GeneratedStatementPrefixFamily.mapCursor head convert) invariant) next.1,
      fun {state} => accepted_generated_invariant_stopped_sequence_cons selected before none bindings want block invariant advance
        (GeneratedStoppedStatementPrefixFamily.withInvariant stopped invariant) next.2⟩


theorem accepted_generated_recursive_if_statements_prepend {cfg : Cfg} {env : Env} {statements : List Stmt}
    (fragment : RecursiveIfStatements cfg env statements) :
    ∀ {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
      (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
      (before : LS) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block) {rest : List Stmt},
      (GeneratedSequencePrefixFamily cx results selected before none bindings want block rest
        (@WhileMixedStatementCursor cfg env cx results root owner selected) ∧
       GeneratedStoppedSequencePrefixFamily cx results selected before none bindings want block rest) →
      GeneratedSequencePrefixFamily cx results selected before none bindings want block (statements ++ rest)
        (@WhileMixedStatementCursor cfg env cx results root owner selected) ∧
      GeneratedStoppedSequencePrefixFamily cx results selected before none bindings want block (statements ++ rest) := by
  intro cx results root owner selected before bindings want block rest tail
  have invariantTail : InvariantSequencePrefixFamily cx results selected before none bindings want block rest
      (@WhileMixedStatementCursor cfg env cx results root owner selected) (fun _ => True) ∧
      InvariantStoppedSequencePrefixFamily cx results selected before none bindings want block rest (fun _ => True) := by
    constructor
    · intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps
      exact tail.1 source owned occurrence all scope value rows coverage admitted bounded realized input extended steps
    · intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps fuel stop after stopped nonTimeout
      exact tail.2 source owned occurrence all scope value rows coverage admitted bounded realized input extended steps stopped nonTimeout
  have result := accepted_generated_invariant_recursive_if_statements_prepend fragment selected before bindings want block
    (@WhileMixedStatementCursor cfg env cx results root owner selected) (by
      intro statement state source before built initial start map required runtime current
      exact current)
    (fun _ => True) (fun _ _ => trivial) invariantTail
  constructor
  · intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended taken reached steps
    exact result.1 source owned occurrence all scope value rows coverage admitted bounded realized input extended trivial steps
  · intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended taken reached steps fuel stop after stopped nonTimeout
    exact result.2 source owned occurrence all scope value rows coverage admitted bounded realized input extended trivial steps stopped nonTimeout

theorem accepted_generated_invariant_while_mixed_prepend {cfg : Cfg} {env : Env} {statements : List Stmt}
    (fragment : WhileMixedStatements cfg env statements) :
    ∀ {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
      (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
      (before : LS) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block)
      (cursor : ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
        LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
      (convert : ∀ {statement : Stmt} {state : St} (source : StmtSource cfg env statement state)
        {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
        WhileMixedStatementCursor cx results selected source before built initial start map required runtime →
          cursor source before built initial start map required runtime)
      (invariant : DemandRuntimePoint → Prop)
      (advance : ∀ {length : Nat} {first last : DemandRuntimePoint}, invariant first → DemandRuntimePrefix cx length first last → invariant last)
      {rest : List Stmt},
      (InvariantSequencePrefixFamily cx results selected before none bindings want block rest cursor invariant ∧
        InvariantStoppedSequencePrefixFamily cx results selected before none bindings want block rest invariant) →
      InvariantSequencePrefixFamily cx results selected before none bindings want block (statements ++ rest) cursor invariant ∧
        InvariantStoppedSequencePrefixFamily cx results selected before none bindings want block (statements ++ rest) invariant := by
  induction fragment with
  | nil =>
    intro cx results root owner selected before bindings want block cursor convert invariant advance rest tail
    simpa using tail
  | scalar fragment tail ih =>
    intro cx results root owner selected before bindings want block cursor convert invariant advance rest restFamily
    simpa only [List.append_assoc] using
      (accepted_generated_invariant_scalar_assignment_statements_prepend selected before none bindings want block fragment cursor
        (by intro statement state source before built initial start map required runtime current; exact convert source (.scalar current))
        invariant advance (ih selected before bindings want block cursor convert invariant advance restFamily))
  | recursive fragment tail ih =>
    intro cx results root owner selected before bindings want block cursor convert invariant advance rest restFamily
    simpa only [List.append_assoc] using
      (accepted_generated_invariant_recursive_if_statements_prepend fragment selected before bindings want block cursor convert invariant advance
        (ih selected before bindings want block cursor convert invariant advance restFamily))
  | loop condition body origin form fragment noValue tail ih =>
    intro cx results root owner selected before bindings want block cursor convert invariant advance rest restFamily
    have agreement := accepted_generated_while_agreement selected condition body origin form fragment noValue
    have head : GeneratedStatementPrefixFamily cx results selected none (.while condition body origin) cursor := by
      apply GeneratedStatementPrefixFamily.mapCursor agreement.1
      intro statement state source before built initial start map required runtime current
      exact convert source (.loop current)
    have tailFamily := ih selected before bindings want block cursor convert invariant advance restFamily
    exact ⟨accepted_generated_invariant_sequence_prefix_cons selected before none bindings want block cursor invariant advance
        (GeneratedStatementPrefixFamily.withInvariant head invariant) tailFamily.1,
      accepted_generated_invariant_stopped_sequence_cons selected before none bindings want block invariant advance
        (GeneratedStoppedStatementPrefixFamily.withInvariant agreement.2 invariant) tailFamily.2⟩

theorem accepted_generated_while_mixed_statements {cfg : Cfg} {env : Env} {statements : List Stmt}
    (fragment : WhileMixedStatements cfg env statements) :
    ∀ {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
      (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
      (before : LS) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block),
      GeneratedSequencePrefixFamily cx results selected before none bindings want block statements
        (@WhileMixedStatementCursor cfg env cx results root owner selected) ∧
      GeneratedStoppedSequencePrefixFamily cx results selected before none bindings want block statements := by
  intro cx results root owner selected before bindings want block
  have tail : InvariantSequencePrefixFamily cx results selected before none bindings want block []
      (@WhileMixedStatementCursor cfg env cx results root owner selected) (fun _ => True) ∧
      InvariantStoppedSequencePrefixFamily cx results selected before none bindings want block [] (fun _ => True) := by
    constructor
    · intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps
      exact accepted_generated_sequence_prefix_nil selected before none bindings want block _ source owned occurrence all scope value rows coverage admitted bounded realized input extended steps
    · intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps fuel stop after stopped nonTimeout
      exact accepted_generated_stopped_sequence_nil selected before none bindings want block source owned occurrence all scope value rows coverage admitted bounded realized input extended steps stopped nonTimeout
  have result := accepted_generated_invariant_while_mixed_prepend fragment selected before bindings want block
    (@WhileMixedStatementCursor cfg env cx results root owner selected) (by
      intro statement state source before built initial start map required runtime current
      exact current) (fun _ => True) (fun _ _ => trivial) tail
  simp only [List.append_nil] at result
  constructor
  · intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended taken reached steps
    simpa using result.1 source owned occurrence all scope value rows coverage admitted bounded realized input extended trivial steps
  · intro state source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended taken reached steps fuel stop after stopped nonTimeout
    simpa using result.2 source owned occurrence all scope value rows coverage admitted bounded realized input extended trivial steps stopped nonTimeout


#print axioms accepted_generated_invariant_while_mixed_prepend

#print axioms accepted_generated_recursive_if_statements_prepend
#print axioms accepted_generated_while_mixed_statements
#print axioms WhileMixedStatements.normal
end Goose.Lower
