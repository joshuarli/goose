import Goose.Lower.Range
import Goose.Core.Sound.Check

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem tyStmt_range_scope (env : TEnv) (sc : Nat) (x : VarId) (lo hi : Expr)
    (body : Core.Block) (org : OriginId) (next next' : Nat) (env' : TEnv)
    (h : tyStmt env sc (.forRange x lo hi body org) next = .ok (env', next')) :
    ∃ lv, env.vars[x]? = some lv ∧ lv.scope = body.scope := by
  rw [tyStmt] at h
  obtain ⟨_, middle, _, hrest⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp h
  obtain ⟨lv, after, hdeclare, _⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp hrest
  obtain ⟨_, hvar, hscope, _, _⟩ := Core.Sound.declare_ok env x body.scope middle (lv, after) hdeclare
  exact ⟨lv, hvar, hscope⟩

theorem tyStmt_range_children (env : TEnv) (sc : Nat) (x : VarId) (lo hi : Expr)
    (body : Core.Block) (org : OriginId) (next next' : Nat) (env' : TEnv)
    (h : tyStmt env sc (.forRange x lo hi body org) next = .ok (env', next')) :
    ∃ lowerTy lowerStart lowerNext upperTy upperStart upperNext bodyTy bodyStart bodyNext,
      tyExpr env lo lowerStart = .ok (lowerTy, lowerNext) ∧
      tyExpr env hi upperStart = .ok (upperTy, upperNext) ∧
      tyBlock { env with loops := env.loops + 1, visible := x :: env.visible } [] body bodyStart =
        .ok (bodyTy, bodyNext) := by
  rw [tyStmt] at h
  obtain ⟨_, _, _, h⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp h
  obtain ⟨_, lowerStart, _, h⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp h
  obtain ⟨lowerTy, lowerNext, hLower, h⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp h
  obtain ⟨_, upperStart, _, h⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp h
  obtain ⟨upperTy, upperNext, hUpper, h⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp h
  obtain ⟨_, _, _, h⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp h
  split at h
  · obtain ⟨_, bodyStart, _, h⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp h
    obtain ⟨bodyTy, bodyNext, hBody, _⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp h
    exact ⟨lowerTy, lowerStart, lowerNext, upperTy, upperStart, upperNext,
      bodyTy, bodyStart, bodyNext, hLower, hUpper, hBody⟩
  · simp only [Core.Sound.st_bind_ok, Core.Sound.rej_ok, false_and, exists_false] at h

theorem stmt_range_sim_of_typed (n : Nat) (lc : Option LoopCtx) (x : VarId) (lo hi : Expr)
    (body : Core.Block) (org : OriginId)
    (hokLo : exprOk lo = true) (hokHi : exprOk hi = true) (hokBody : blockOk body = true)
    (le : LEnv) (ls ls' : LS) (r : Unit) (pt : Pt) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (fr : Frame) (source after : TEnv) (sc next next' : Nat) (hvars : source.vars = env.vars)
    (htype : tyStmt source sc (.forRange x lo hi body org) next = .ok (after, next'))
    (hlow : lowerStmt lc (.forRange x lo hi body org) le ls = (r, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls) :
    SimG cx pt fr (execStmt n cfg env (.forRange x lo hi body org)) (fun flow pt' fr' =>
      flow = .normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' []) := by
  have hscope := tyStmt_range_scope source sc x lo hi body org next next' after htype
  rw [hvars] at hscope
  exact stmt_range_sim n lc x lo hi body org hokLo hokHi hokBody
    le ls ls' r pt cfg env cx fr hscope hlow hpp hext hrel

end Goose.Lower
