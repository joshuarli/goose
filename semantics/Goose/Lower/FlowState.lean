import Goose.Lower.ReturnState

namespace Goose.Lower

open Goose.Core Goose.GIR

def ReturnedAt (cx : FnCtx) (flow : Flow) (pt : Pt) (fr : GIR.Frame) : Prop :=
  ∃ value org, flow = .ret value ∧ ReturnSite cx pt fr value org

def StmtFlowPost (cfg : Cfg) (env : Env) (cx : FnCtx) (ls : LS) (fr : GIR.Frame)
    (ls' : LS) (flow : Flow) (pt' : Pt) (fr' : GIR.Frame) : Prop :=
  (flow = .normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' []) ∨ ReturnedAt cx flow pt' fr'

def returnStmtsTail (n : Nat) (cfg : Cfg) (env : Env) (rest : List Stmt) : Flow → M Flow
  | .normal _ => execStmts n cfg env rest >>= prepareReturn env
  | flow => pure flow

theorem prepareReturn_execStmts (n : Nat) (cfg : Cfg) (env : Env)
    (stmt : Stmt) (rest : List Stmt) :
    (execStmts (n + 1) cfg env (stmt :: rest) >>= prepareReturn env) =
      ((execStmt n cfg env stmt >>= prepareReturn env) >>= returnStmtsTail n cfg env rest) := by
  simp only [execStmts, bind_assoc]
  congr 1
  funext flow
  cases flow <;> simp [prepareReturn, returnStmtsTail, bind_assoc, pure_bind]

def BlockFlowPost (cfg : Cfg) (env : Env) (cx : FnCtx) (ls : LS) (fr : GIR.Frame)
    (ls' : LS) (blk : Core.Block) (want : Bool) (r : ValueId)
    (flow : Flow) (pt' : Pt) (fr' : GIR.Frame) : Prop :=
  (∃ value, flow = .normal value ∧ (blk.value = none → value = .unit) ∧
    Post cfg env cx ls fr ls' fr' pt' (blockCells blk want r value)) ∨
    ReturnedAt cx flow pt' fr'


def unitFlow : Flow → Flow
  | .normal _ => .normal .unit
  | flow => flow

theorem prepareReturn_unitFlow (env : Env) (flow : Flow) :
    (prepareReturn env (unitFlow flow)) =
      (prepareReturn env flow >>= fun flow' => pure (unitFlow flow')) := by
  cases flow <;> simp [unitFlow, prepareReturn, bind_assoc, pure_bind]

def preparedIf (n : Nat) (cfg : Cfg) (env : Env) (c : Expr)
    (t : Core.Block) (f : Option Core.Block) : M Flow := do
  let branch ← expectBool (← evalExpr n cfg env c)
  let flow ← if branch then execBlock n cfg env [] t >>= prepareReturn env
    else match f with
      | some block => execBlock n cfg env [] block >>= prepareReturn env
      | none => pure (.normal .unit)
  pure (unitFlow flow)

theorem prepareReturn_ifStmt (n : Nat) (cfg : Cfg) (env : Env) (c : Expr)
    (t : Core.Block) (f : Option Core.Block) (org : OriginId) :
    (execStmt (n + 1) cfg env (.ifS c t f org) >>= prepareReturn env) =
      preparedIf n cfg env c t f := by
  simp only [execStmt, preparedIf, bind_assoc]
  congr 1
  funext value
  congr 1
  funext branch
  cases branch <;> cases f <;> simp only [Bool.false_eq_true, ↓reduceIte, pure_bind,
    unitFlow, prepareReturn, bind_assoc]
  all_goals
    congr 1
    funext flow
    cases flow <;> simp [prepareReturn, unitFlow, bind_assoc, pure_bind]


end Goose.Lower
