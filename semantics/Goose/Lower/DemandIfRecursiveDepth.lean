import Goose.Lower.DemandIfRecursiveSyntax

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive BoundedIfStatements (cfg : Cfg) : Nat → Env → List Stmt → Prop
  | nil (depth : Nat) (env : Env) : BoundedIfStatements cfg depth env []
  | scalar {depth : Nat} {env : Env} {segment rest : List Stmt}
      (fragment : ScalarAssignmentStatements cfg env segment) (tail : BoundedIfStatements cfg depth env rest) :
      BoundedIfStatements cfg depth env (segment ++ rest)
  | conditional {depth : Nat} {env : Env} {condition : Expr} (form : ControlPrefixExpression condition) (yes : Core.Block) (origin : OriginId)
      (branch : ∀ state : St, BoundedIfStatements cfg depth
        { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
      (noValue : yes.value = none) {rest : List Stmt} (tail : BoundedIfStatements cfg (depth + 1) env rest) :
      BoundedIfStatements cfg (depth + 1) env (.ifS condition yes none origin :: rest)
  | conditionalElse {depth : Nat} {env : Env} {condition : Expr} (form : ControlPrefixExpression condition) (yes no : Core.Block) (origin : OriginId)
      (yesBranch : ∀ state : St, BoundedIfStatements cfg depth
        { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
      (noBranch : ∀ state : St, BoundedIfStatements cfg depth
        { env with scopes := (no.scope, state.nextScope) :: env.scopes } no.stmts)
      (yesNoValue : yes.value = none) (noNoValue : no.value = none) {rest : List Stmt}
      (tail : BoundedIfStatements cfg (depth + 1) env rest) :
      BoundedIfStatements cfg (depth + 1) env (.ifS condition yes (some no) origin :: rest)

theorem BoundedIfStatements.mono {cfg : Cfg} {depth larger : Nat} {env : Env} {statements : List Stmt}
    (form : BoundedIfStatements cfg depth env statements) (bound : depth ≤ larger) : BoundedIfStatements cfg larger env statements := by
  induction form generalizing larger with
  | nil depth env => exact .nil larger env
  | scalar fragment tail ih => exact .scalar fragment (ih bound)
  | @conditional depth env condition form yes origin branch noValue rest tail branchIH tailIH =>
    cases larger with
    | zero => omega
    | succ larger => exact .conditional form yes origin (fun state => branchIH state (by omega)) noValue (tailIH bound)
  | @conditionalElse depth env condition form yes no origin yesBranch noBranch yesNoValue noNoValue rest tail yesIH noIH tailIH =>
    cases larger with
    | zero => omega
    | succ larger =>
      apply BoundedIfStatements.conditionalElse form yes no origin
      · intro state; exact yesIH state (by omega)
      · intro state; exact noIH state (by omega)
      · exact yesNoValue
      · exact noNoValue
      · exact tailIH (by omega)

theorem statementsSize_append_le (segment rest : List Stmt) :
    Place._sizeOf_11 rest ≤ Place._sizeOf_11 (segment ++ rest) := by
  induction segment with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
    change Place._sizeOf_11 rest ≤ 1 + Place._sizeOf_8 head + Place._sizeOf_11 (tail ++ rest)
    omega

theorem RecursiveIfStatements.bounded {cfg : Cfg} {env : Env} {statements : List Stmt}
    (form : RecursiveIfStatements cfg env statements) : BoundedIfStatements cfg (Place._sizeOf_11 statements) env statements := by
  induction form with
  | nil env => exact .nil _ env
  | @scalar env segment rest fragment tail ih =>
    apply BoundedIfStatements.scalar fragment
    apply ih.mono
    exact statementsSize_append_le segment rest
  | @conditional env condition form yes origin branch noValue rest tail branchIH tailIH =>
    have branchBound : Place._sizeOf_11 yes.stmts < Place._sizeOf_11 (.ifS condition yes none origin :: rest : List Stmt) := by
      cases yes <;> simp [Core.Block.stmts, Place._sizeOf_11, sizeOf] <;> omega
    have tailBound : Place._sizeOf_11 rest < Place._sizeOf_11 (.ifS condition yes none origin :: rest : List Stmt) := by
      simp [Place._sizeOf_11, sizeOf] <;> omega
    cases totalEq : Place._sizeOf_11 (.ifS condition yes none origin :: rest : List Stmt) with
    | zero => omega
    | succ total =>
      apply BoundedIfStatements.conditional form yes origin
      · intro state
        apply (branchIH state).mono
        omega
      · exact noValue
      · apply tailIH.mono
        omega
  | @conditionalElse env condition form yes no origin yesBranch noBranch yesNoValue noNoValue rest tail yesIH noIH tailIH =>
    have yesBound : Place._sizeOf_11 yes.stmts < Place._sizeOf_11 (.ifS condition yes (some no) origin :: rest : List Stmt) := by
      cases yes <;> simp [Core.Block.stmts, Place._sizeOf_11, sizeOf] <;> omega
    have noBound : Place._sizeOf_11 no.stmts < Place._sizeOf_11 (.ifS condition yes (some no) origin :: rest : List Stmt) := by
      cases no <;> simp [Core.Block.stmts, Place._sizeOf_11, sizeOf] <;> omega
    have tailBound : Place._sizeOf_11 rest < Place._sizeOf_11 (.ifS condition yes (some no) origin :: rest : List Stmt) := by
      simp [Place._sizeOf_11, sizeOf] <;> omega
    cases totalEq : Place._sizeOf_11 (.ifS condition yes (some no) origin :: rest : List Stmt) with
    | zero => omega
    | succ total =>
      apply BoundedIfStatements.conditionalElse form yes no origin
      · intro state
        apply (yesIH state).mono
        omega
      · intro state
        apply (noIH state).mono
        omega
      · exact yesNoValue
      · exact noNoValue
      · apply tailIH.mono
        omega

theorem BoundedIfStatements.recursive {cfg : Cfg} {depth : Nat} {env : Env} {statements : List Stmt}
    (form : BoundedIfStatements cfg depth env statements) : RecursiveIfStatements cfg env statements := by
  induction form with
  | nil depth env => exact .nil env
  | scalar fragment tail ih => exact .scalar fragment ih
  | conditional form yes origin branch noValue tail branchIH tailIH =>
    exact .conditional form yes origin branchIH noValue tailIH
  | conditionalElse form yes no origin yesBranch noBranch yesNoValue noNoValue tail yesIH noIH tailIH =>
    exact .conditionalElse form yes no origin yesIH noIH yesNoValue noNoValue tailIH

#print axioms BoundedIfStatements.recursive
#print axioms BoundedIfStatements.mono
#print axioms RecursiveIfStatements.bounded
end Goose.Lower
