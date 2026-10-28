import Goose.Lower.DemandIfNestedBlock

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive RecursiveIfStatements (cfg : Cfg) : Env → List Stmt → Prop
  | nil (env : Env) : RecursiveIfStatements cfg env []
  | scalar {env : Env} {segment rest : List Stmt} (fragment : ScalarAssignmentStatements cfg env segment)
      (tail : RecursiveIfStatements cfg env rest) : RecursiveIfStatements cfg env (segment ++ rest)
  | conditional {env : Env} {condition : Expr} (form : ControlPrefixExpression condition) (yes : Core.Block) (origin : OriginId)
      (branch : ∀ state : St, RecursiveIfStatements cfg
        { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
      (noValue : yes.value = none) {rest : List Stmt} (tail : RecursiveIfStatements cfg env rest) :
      RecursiveIfStatements cfg env (.ifS condition yes none origin :: rest)
  | conditionalElse {env : Env} {condition : Expr} (form : ControlPrefixExpression condition) (yes no : Core.Block) (origin : OriginId)
      (yesBranch : ∀ state : St, RecursiveIfStatements cfg
        { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
      (noBranch : ∀ state : St, RecursiveIfStatements cfg
        { env with scopes := (no.scope, state.nextScope) :: env.scopes } no.stmts)
      (yesNoValue : yes.value = none) (noNoValue : no.value = none) {rest : List Stmt} (tail : RecursiveIfStatements cfg env rest) :
      RecursiveIfStatements cfg env (.ifS condition yes (some no) origin :: rest)

theorem RecursiveIfStatements.fragment {cfg : Cfg} {env : Env} {statements : List Stmt}
    (form : RecursiveIfStatements cfg env statements) : stmtsOk statements = true := by
  induction form with
  | nil => rfl
  | scalar fragment tail ih => exact stmtsOk_append fragment.fragment ih
  | conditional condition yes origin branch noValue tail branchIH ih =>
    have valid := branchIH St.initial
    cases yes with
    | mk scope statements value =>
      simp only [Core.Block.value] at noValue
      subst value
      simp only [Core.Block.stmts] at valid
      simp [stmtsOk, stmtOk, blockOk, condition.fragment, valid, ih]
  | conditionalElse condition yes no origin yesBranch noBranch yesNoValue noNoValue tail yesIH noIH ih =>
    have yesValid := yesIH St.initial
    have noValid := noIH St.initial
    cases yes with
    | mk yesScope yesStatements yesValue =>
      cases no with
      | mk noScope noStatements noValue =>
        simp only [Core.Block.value] at yesNoValue noNoValue
        subst yesValue
        subst noValue
        simp only [Core.Block.stmts] at yesValid noValid
        simp [stmtsOk, stmtOk, blockOk, condition.fragment, yesValid, noValid, ih]

theorem RecursiveIfStatements.normal {cfg : Cfg} {env : Env} {statements : List Stmt}
    (form : RecursiveIfStatements cfg env statements) {fuel : Nat} {state after : St} {flow : Flow}
    (done : execStmts fuel cfg env statements state = .ok flow after) : flow = .normal .unit :=
  stmts_fragment_normal form.fragment done

theorem IfMixedStatements.recursive {cfg : Cfg} {env : Env} {statements : List Stmt}
    (form : IfMixedStatements cfg env statements) : RecursiveIfStatements cfg env statements := by
  induction form with
  | nil => exact .nil _
  | scalar fragment tail ih => exact .scalar fragment ih
  | conditional form yes origin branch noValue tail ih =>
    apply RecursiveIfStatements.conditional form yes origin _ noValue ih
    intro state
    simpa using RecursiveIfStatements.scalar (branch state) (.nil _)
  | conditionalElse form yes no origin yesBranch noBranch yesNoValue noNoValue tail ih =>
    apply RecursiveIfStatements.conditionalElse form yes no origin _ _ yesNoValue noNoValue ih
    · intro state
      simpa using RecursiveIfStatements.scalar (yesBranch state) (.nil _)
    · intro state
      simpa using RecursiveIfStatements.scalar (noBranch state) (.nil _)

theorem NestedIfMixedStatements.recursive {cfg : Cfg} {env : Env} {statements : List Stmt}
    (form : NestedIfMixedStatements cfg env statements) : RecursiveIfStatements cfg env statements := by
  induction form with
  | nil => exact .nil _
  | scalar fragment tail ih => exact .scalar fragment ih
  | conditionalElse form yes no origin yesBranch noBranch yesNoValue noNoValue tail ih =>
    exact .conditionalElse form yes no origin (fun state => (yesBranch state).recursive)
      (fun state => (noBranch state).recursive) yesNoValue noNoValue ih

#print axioms IfMixedStatements.recursive
#print axioms NestedIfMixedStatements.recursive
#print axioms RecursiveIfStatements.normal
end Goose.Lower
