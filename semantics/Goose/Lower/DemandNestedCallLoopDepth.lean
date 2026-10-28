import Goose.Lower.DemandCallLoopMixedNormal

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive NestedCallLoopStatements (cfg : Cfg) : Env → List Stmt → Prop
  | mixed {env : Env} {statements : List Stmt} (fragment : ReachableScalarCallStatements cfg env statements) :
      NestedCallLoopStatements cfg env statements
  | conditional {env : Env} (condition : Expr) (yes : Core.Block) (origin : OriginId)
      (conditionForm : ControlPrefixExpression condition)
      (yesForm : ∀ middle : St, NestedCallLoopStatements cfg
        { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } yes.stmts)
      (noValue : yes.value = none) {later : List Stmt} (tail : NestedCallLoopStatements cfg env later) :
      NestedCallLoopStatements cfg env (.ifS condition yes none origin :: later)
  | conditionalElse {env : Env} (condition : Expr) (yes no : Core.Block) (origin : OriginId)
      (conditionForm : ControlPrefixExpression condition)
      (yesForm : ∀ middle : St, NestedCallLoopStatements cfg
        { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } yes.stmts)
      (noForm : ∀ middle : St, NestedCallLoopStatements cfg
        { env with scopes := (no.scope, middle.nextScope) :: env.scopes } no.stmts)
      (yesNoValue : yes.value = none) (noNoValue : no.value = none)
      {later : List Stmt} (tail : NestedCallLoopStatements cfg env later) :
      NestedCallLoopStatements cfg env (.ifS condition yes (some no) origin :: later)
  | loop {env : Env} (condition : Expr) (body : Core.Block) (origin : OriginId)
      (conditionForm : ControlPrefixExpression condition)
      (bodyForm : ∀ middle : St, NestedCallLoopStatements cfg
        { env with scopes := (body.scope, middle.nextScope) :: env.scopes } body.stmts)
      (noValue : body.value = none) {later : List Stmt} (tail : NestedCallLoopStatements cfg env later) :
      NestedCallLoopStatements cfg env (.while condition body origin :: later)

inductive BoundedNestedCallLoopStatements (cfg : Cfg) : Nat → Env → List Stmt → Prop
  | mixed {depth : Nat} {env : Env} {statements : List Stmt} (fragment : ReachableScalarCallStatements cfg env statements) :
      BoundedNestedCallLoopStatements cfg depth env statements
  | conditional {depth : Nat} {env : Env} (condition : Expr) (yes : Core.Block) (origin : OriginId)
      (conditionForm : ControlPrefixExpression condition)
      (yesForm : ∀ middle : St, BoundedNestedCallLoopStatements cfg depth
        { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } yes.stmts)
      (noValue : yes.value = none) {later : List Stmt} (tail : BoundedNestedCallLoopStatements cfg (depth + 1) env later) :
      BoundedNestedCallLoopStatements cfg (depth + 1) env (.ifS condition yes none origin :: later)
  | conditionalElse {depth : Nat} {env : Env} (condition : Expr) (yes no : Core.Block) (origin : OriginId)
      (conditionForm : ControlPrefixExpression condition)
      (yesForm : ∀ middle : St, BoundedNestedCallLoopStatements cfg depth
        { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } yes.stmts)
      (noForm : ∀ middle : St, BoundedNestedCallLoopStatements cfg depth
        { env with scopes := (no.scope, middle.nextScope) :: env.scopes } no.stmts)
      (yesNoValue : yes.value = none) (noNoValue : no.value = none)
      {later : List Stmt} (tail : BoundedNestedCallLoopStatements cfg (depth + 1) env later) :
      BoundedNestedCallLoopStatements cfg (depth + 1) env (.ifS condition yes (some no) origin :: later)
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
  | @conditional depth env condition yes origin conditionForm yesForm noValue later tail yesIH tailIH =>
    cases larger with
    | zero => omega
    | succ larger => exact .conditional condition yes origin conditionForm (fun middle => yesIH middle (by omega)) noValue (tailIH bound)
  | @conditionalElse depth env condition yes no origin conditionForm yesForm noForm yesNoValue noNoValue later tail yesIH noIH tailIH =>
    cases larger with
    | zero => omega
    | succ larger =>
      apply BoundedNestedCallLoopStatements.conditionalElse condition yes no origin conditionForm
      · intro middle; exact yesIH middle (by omega)
      · intro middle; exact noIH middle (by omega)
      · exact yesNoValue
      · exact noNoValue
      · exact tailIH bound
  | @loop depth env condition body origin conditionForm bodyForm noValue later tail bodyIH tailIH =>
    cases larger with
    | zero => omega
    | succ larger => exact .loop condition body origin conditionForm (fun middle => bodyIH middle (by omega)) noValue (tailIH bound)

theorem NestedCallLoopStatements.bounded {cfg : Cfg} {env : Env} {statements : List Stmt}
    (form : NestedCallLoopStatements cfg env statements) :
    BoundedNestedCallLoopStatements cfg (Place._sizeOf_11 statements) env statements := by
  induction form with
  | mixed fragment => exact .mixed fragment
  | @conditional env condition yes origin conditionForm yesForm noValue later tail yesIH tailIH =>
    have bodyBound : Place._sizeOf_11 yes.stmts < Place._sizeOf_11 (.ifS condition yes none origin :: later : List Stmt) := by
      cases yes <;> simp [Core.Block.stmts, Place._sizeOf_11, sizeOf] <;> omega
    have tailBound : Place._sizeOf_11 later < Place._sizeOf_11 (.ifS condition yes none origin :: later : List Stmt) := by
      simp [Place._sizeOf_11, sizeOf] <;> omega
    cases totalEq : Place._sizeOf_11 (.ifS condition yes none origin :: later : List Stmt) with
    | zero => omega
    | succ total =>
      apply BoundedNestedCallLoopStatements.conditional condition yes origin conditionForm
      · intro middle; apply (yesIH middle).mono; omega
      · exact noValue
      · apply tailIH.mono; omega
  | @conditionalElse env condition yes no origin conditionForm yesForm noForm yesNoValue noNoValue later tail yesIH noIH tailIH =>
    have yesBound : Place._sizeOf_11 yes.stmts < Place._sizeOf_11 (.ifS condition yes (some no) origin :: later : List Stmt) := by
      cases yes <;> simp [Core.Block.stmts, Place._sizeOf_11, sizeOf] <;> omega
    have noBound : Place._sizeOf_11 no.stmts < Place._sizeOf_11 (.ifS condition yes (some no) origin :: later : List Stmt) := by
      cases no <;> simp [Core.Block.stmts, Place._sizeOf_11, sizeOf] <;> omega
    have tailBound : Place._sizeOf_11 later < Place._sizeOf_11 (.ifS condition yes (some no) origin :: later : List Stmt) := by
      simp [Place._sizeOf_11, sizeOf] <;> omega
    cases totalEq : Place._sizeOf_11 (.ifS condition yes (some no) origin :: later : List Stmt) with
    | zero => omega
    | succ total =>
      apply BoundedNestedCallLoopStatements.conditionalElse condition yes no origin conditionForm
      · intro middle; apply (yesIH middle).mono; omega
      · intro middle; apply (noIH middle).mono; omega
      · exact yesNoValue
      · exact noNoValue
      · apply tailIH.mono; omega
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
  | @conditional env condition yes origin conditionForm yesForm noValue later tail yesIH tailIH =>
    cases fuel with
    | zero => simp [execStmts, timeout, M.stop] at done
    | succ fuel =>
      simp only [execStmts, bind_apply] at done
      cases head : execStmt fuel cfg other (.ifS condition yes none origin) state with
      | stop reason final => simp only [head] at done; cases done
      | ok first middle =>
        have normal : first = .normal .unit := by
          cases fuel with
          | zero => simp [execStmt, timeout, M.stop] at head
          | succ fuel =>
            simp only [execStmt] at head
            obtain ⟨value, afterExpr, _, rest⟩ := call_loop_bind_ok head
            obtain ⟨choice, afterTest, _, rest⟩ := call_loop_bind_ok rest
            cases choice with
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, pure_apply, Res.ok.injEq] at rest
              exact rest.1.symm
            | true =>
              obtain ⟨branchFlow, afterBranch, branchDone, rest⟩ := call_loop_bind_ok rest
              have bodyNormal : ∀ {innerEnv : Env} {fuel : Nat} {state after : St} {flow : Flow},
                  execStmts fuel cfg innerEnv yes.stmts state = .ok flow after → flow = .normal .unit := by
                intro innerEnv fuel state after flow result
                exact yesIH St.initial result
              have branchNormal := call_block_normal_of_stmts bodyNormal noValue branchDone
              subst branchFlow
              simpa [pure_apply] using (Res.ok.inj rest).1.symm
        subst first
        simp only [head] at done
        exact tailIH done
  | @conditionalElse env condition yes no origin conditionForm yesForm noForm yesNoValue noNoValue later tail yesIH noIH tailIH =>
    cases fuel with
    | zero => simp [execStmts, timeout, M.stop] at done
    | succ fuel =>
      simp only [execStmts, bind_apply] at done
      cases head : execStmt fuel cfg other (.ifS condition yes (some no) origin) state with
      | stop reason final => simp only [head] at done; cases done
      | ok first middle =>
        have normal : first = .normal .unit := by
          cases fuel with
          | zero => simp [execStmt, timeout, M.stop] at head
          | succ fuel =>
            simp only [execStmt] at head
            obtain ⟨value, afterExpr, _, rest⟩ := call_loop_bind_ok head
            obtain ⟨choice, afterTest, _, rest⟩ := call_loop_bind_ok rest
            cases choice with
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at rest
              obtain ⟨branchFlow, afterBranch, branchDone, rest⟩ := call_loop_bind_ok rest
              have bodyNormal : ∀ {innerEnv : Env} {fuel : Nat} {state after : St} {flow : Flow},
                  execStmts fuel cfg innerEnv no.stmts state = .ok flow after → flow = .normal .unit := by
                intro innerEnv fuel state after flow result
                exact noIH St.initial result
              have branchNormal := call_block_normal_of_stmts bodyNormal noNoValue branchDone
              subst branchFlow
              simpa [pure_apply] using (Res.ok.inj rest).1.symm
            | true =>
              obtain ⟨branchFlow, afterBranch, branchDone, rest⟩ := call_loop_bind_ok rest
              have bodyNormal : ∀ {innerEnv : Env} {fuel : Nat} {state after : St} {flow : Flow},
                  execStmts fuel cfg innerEnv yes.stmts state = .ok flow after → flow = .normal .unit := by
                intro innerEnv fuel state after flow result
                exact yesIH St.initial result
              have branchNormal := call_block_normal_of_stmts bodyNormal yesNoValue branchDone
              subst branchFlow
              simpa [pure_apply] using (Res.ok.inj rest).1.symm
        subst first
        simp only [head] at done
        exact tailIH done
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
  | conditional condition yes origin conditionForm yesForm noValue tail yesIH tailIH =>
    exact .conditional condition yes origin conditionForm yesIH noValue tailIH
  | conditionalElse condition yes no origin conditionForm yesForm noForm yesNoValue noNoValue tail yesIH noIH tailIH =>
    exact .conditionalElse condition yes no origin conditionForm yesIH noIH yesNoValue noNoValue tailIH
  | loop condition body origin conditionForm bodyForm noValue tail bodyIH tailIH =>
    exact .loop condition body origin conditionForm bodyIH noValue tailIH

#print axioms NestedCallLoopStatements.normal_any_env
#print axioms BoundedNestedCallLoopStatements.recursive

#print axioms BoundedNestedCallLoopStatements.mono
#print axioms NestedCallLoopStatements.bounded
end Goose.Lower
