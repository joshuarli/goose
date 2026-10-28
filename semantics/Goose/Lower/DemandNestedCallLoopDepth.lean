import Goose.Lower.DemandNestedCallLoopBody

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive NestedCallLoopStatements (cfg : Cfg) : Env → List Stmt → Prop
  | mixed {env : Env} {statements : List Stmt} (fragment : ReachableScalarCallStatements cfg env statements) :
      NestedCallLoopStatements cfg env statements
  | loop {env : Env} (condition : Expr) (body : Core.Block) (origin : OriginId)
      (conditionForm : ControlPrefixExpression condition)
      (bodyForm : ∀ middle : St, NestedCallLoopStatements cfg
        { env with scopes := (body.scope, middle.nextScope) :: env.scopes } body.stmts)
      (noValue : body.value = none) {later : List Stmt} (tail : NestedCallLoopStatements cfg env later) :
      NestedCallLoopStatements cfg env (.while condition body origin :: later)

inductive BoundedNestedCallLoopStatements (cfg : Cfg) : Nat → Env → List Stmt → Prop
  | mixed {depth : Nat} {env : Env} {statements : List Stmt} (fragment : ReachableScalarCallStatements cfg env statements) :
      BoundedNestedCallLoopStatements cfg depth env statements
  | loop {depth : Nat} {env : Env} (condition : Expr) (body : Core.Block) (origin : OriginId)
      (conditionForm : ControlPrefixExpression condition)
      (bodyForm : ∀ middle : St, BoundedNestedCallLoopStatements cfg depth
        { env with scopes := (body.scope, middle.nextScope) :: env.scopes } body.stmts)
      (noValue : body.value = none) {later : List Stmt} (tail : BoundedNestedCallLoopStatements cfg (depth + 1) env later) :
      BoundedNestedCallLoopStatements cfg (depth + 1) env (.while condition body origin :: later)

theorem BoundedNestedCallLoopStatements.mono {cfg : Cfg} {depth larger : Nat} {env : Env} {statements : List Stmt}
    (form : BoundedNestedCallLoopStatements cfg depth env statements) (bound : depth ≤ larger) :
    BoundedNestedCallLoopStatements cfg larger env statements := by
  induction form generalizing larger with
  | mixed fragment => exact .mixed fragment
  | @loop depth env condition body origin conditionForm bodyForm noValue later tail bodyIH tailIH =>
    cases larger with
    | zero => omega
    | succ larger => exact .loop condition body origin conditionForm (fun middle => bodyIH middle (by omega)) noValue (tailIH bound)

theorem NestedCallLoopStatements.bounded {cfg : Cfg} {env : Env} {statements : List Stmt}
    (form : NestedCallLoopStatements cfg env statements) :
    BoundedNestedCallLoopStatements cfg (Place._sizeOf_11 statements) env statements := by
  induction form with
  | mixed fragment => exact .mixed fragment
  | @loop env condition body origin conditionForm bodyForm noValue later tail bodyIH tailIH =>
    have bodyBound : Place._sizeOf_11 body.stmts < Place._sizeOf_11 (.while condition body origin :: later : List Stmt) := by
      cases body <;> simp [Core.Block.stmts, Place._sizeOf_11, sizeOf] <;> omega
    have tailBound : Place._sizeOf_11 later < Place._sizeOf_11 (.while condition body origin :: later : List Stmt) := by
      simp [Place._sizeOf_11, sizeOf] <;> omega
    cases totalEq : Place._sizeOf_11 (.while condition body origin :: later : List Stmt) with
    | zero => omega
    | succ total =>
      apply BoundedNestedCallLoopStatements.loop condition body origin conditionForm
      · intro middle
        apply (bodyIH middle).mono
        omega
      · exact noValue
      · apply tailIH.mono
        omega

theorem NestedCallLoopStatements.normal_any_env {cfg : Cfg} {env other : Env} {statements : List Stmt}
    (form : NestedCallLoopStatements cfg env statements) {fuel : Nat} {state after : St} {flow : Flow}
    (done : execStmts fuel cfg other statements state = .ok flow after) : flow = .normal .unit := by
  induction form generalizing other fuel state after flow with
  | mixed fragment => exact fragment.normal_any_env done
  | @loop env condition body origin conditionForm bodyForm noValue later tail bodyIH tailIH =>
    cases fuel with
    | zero => simp [execStmts, timeout, M.stop] at done
    | succ fuel =>
      simp only [execStmts, bind_apply] at done
      cases head : execStmt fuel cfg other (.while condition body origin) state with
      | stop reason final => simp only [head] at done; cases done
      | ok first middle =>
        cases fuel with
        | zero => simp [execStmt, timeout, M.stop] at head
        | succ fuel =>
          have bodyNormal : ∀ {innerEnv : Env} {fuel : Nat} {state after : St} {flow : Flow},
              execStmts fuel cfg innerEnv body.stmts state = .ok flow after → flow = .normal .unit := by
            intro innerEnv fuel state after flow result
            exact bodyIH St.initial result
          have normal : first = .normal .unit := call_loop_normal_of_stmts bodyNormal noValue (by simpa [execStmt] using head)
          subst first
          simp only [head] at done
          exact tailIH done

theorem BoundedNestedCallLoopStatements.recursive {cfg : Cfg} {depth : Nat} {env : Env} {statements : List Stmt}
    (form : BoundedNestedCallLoopStatements cfg depth env statements) : NestedCallLoopStatements cfg env statements := by
  induction form with
  | mixed fragment => exact .mixed fragment
  | loop condition body origin conditionForm bodyForm noValue tail bodyIH tailIH =>
    exact .loop condition body origin conditionForm bodyIH noValue tailIH

#print axioms NestedCallLoopStatements.normal_any_env
#print axioms BoundedNestedCallLoopStatements.recursive

#print axioms BoundedNestedCallLoopStatements.mono
#print axioms NestedCallLoopStatements.bounded
end Goose.Lower
