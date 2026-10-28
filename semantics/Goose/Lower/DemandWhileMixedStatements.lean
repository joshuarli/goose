import Goose.Lower.DemandWhileAgreement

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive WhileMixedStatements (cfg : Cfg) (env : Env) : List Stmt → Prop
  | nil : WhileMixedStatements cfg env []
  | scalar {segment rest : List Stmt} (fragment : ScalarAssignmentStatements cfg env segment)
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
  | loop {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : WhileStatementPrefixCursor cx results selected source before built initial start map required runtime) :
      WhileMixedStatementCursor cx results selected source before built initial start map required runtime

theorem WhileMixedStatements.fragment {cfg : Cfg} {env : Env} {statements : List Stmt}
    (form : WhileMixedStatements cfg env statements) : stmtsOk statements = true := by
  induction form with
  | nil => rfl
  | scalar fragment tail ih => exact stmtsOk_append fragment.fragment ih
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

theorem accepted_generated_while_mixed_statements {cfg : Cfg} {env : Env} {statements : List Stmt}
    (fragment : WhileMixedStatements cfg env statements) :
    ∀ {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat}
      (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
      (before : LS) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block),
      GeneratedSequencePrefixFamily cx results selected before none bindings want block statements
        (@WhileMixedStatementCursor cfg env cx results root owner selected) ∧
      GeneratedStoppedSequencePrefixFamily cx results selected before none bindings want block statements := by
  induction fragment with
  | nil =>
    intro cx results root owner selected before bindings want block
    exact ⟨fun {state} => accepted_generated_sequence_prefix_nil selected before none bindings want block _,
      fun {state} => accepted_generated_stopped_sequence_nil selected before none bindings want block⟩
  | scalar fragment tail ih =>
    intro cx results root owner selected before bindings want block
    apply accepted_generated_scalar_assignment_statements_prepend selected before none bindings want block fragment _ ?_
      (ih selected before bindings want block)
    intro statement state source before built initial start map required runtime cursor
    exact .scalar cursor
  | loop condition body origin form fragment noValue tail ih =>
    intro cx results root owner selected before bindings want block
    have agreement := accepted_generated_while_agreement selected condition body origin form fragment noValue
    have head : GeneratedStatementPrefixFamily cx results selected none (.while condition body origin)
        (@WhileMixedStatementCursor cfg env cx results root owner selected) := by
      apply GeneratedStatementPrefixFamily.mapCursor agreement.1
      intro statement state source before built initial start map required runtime cursor
      exact .loop cursor
    exact ⟨fun {state} => accepted_generated_sequence_prefix_cons selected before none bindings want block _ head
        (ih selected before bindings want block).1,
      fun {state} => accepted_generated_stopped_sequence_cons selected before none bindings want block agreement.2
        (ih selected before bindings want block).2⟩

#print axioms accepted_generated_while_mixed_statements
#print axioms WhileMixedStatements.normal
end Goose.Lower
