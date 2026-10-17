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


end Goose.Lower
