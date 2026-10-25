import Goose.Lower.Claims

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem lowerWhile_sim (n : Nat) : WhileClaim n := (claims n).whileLoop

theorem stmt_while_sim (n : Nat) (lc : Option LoopCtx) (c : Expr) (body : Core.Block)
    (org : OriginId) (hokC : exprOk c = true) (hokB : blockOk body = true)
    (le : LEnv) (ls ls' : LS) (r : Unit) (pt : Pt) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (fr : Frame) (hlow : lowerStmt lc (.while c body org) le ls = (r, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls) :
    SimG cx pt fr (execStmt n cfg env (.while c body org)) (fun flow pt' fr' =>
      flow = .normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' []) := by
  cases n with
  | zero => simp only [execStmt]; exact SimG.of_timeout
  | succ n =>
    exact stmtClaim_while n (claims n).whileLoop lc c body org hokC hokB
      le ls ls' r pt cfg env cx fr hlow hpp hext hrel

end Goose.Lower
