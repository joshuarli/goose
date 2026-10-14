import Goose.Lower.ReturnState
import Goose.Lower.Prefix

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem stmt_ret_some_prepared (n : Nat) (lc : Option LoopCtx) (expr : Expr) (org : OriginId)
    (hok : exprOk expr = true) (le : LEnv) (ls ls' : LS) (r : Unit) (pt : Pt)
    (cfg : Cfg) (env : Env) (cx : FnCtx) (fr : GIR.Frame)
    (hlow : lowerStmt lc (.ret (some expr) org) le ls = (r, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls) :
    SimG cx pt fr (execStmt n cfg env (.ret (some expr) org) >>= prepareReturn env)
      (fun flow pt' fr' => ∃ value, flow = .ret value ∧ ReturnSite cx pt' fr' value org) := by
  cases n with
  | zero => simp only [execStmt]; exact SimG.of_timeout_bind
  | succ n =>
    simp only [lowerStmt, bind_eq] at hlow
    obtain ⟨id, middle, hexpr, ids, same, hpure, u, unwound, hleave, hterm⟩ := hlow
    rw [pure_run] at hpure
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpure
    have hextUnwound := hext.of_adv (adv_emitTerm hterm)
    have hextMiddle := hextUnwound.of_adv (advB_leaveTo 0 le middle u unwound hleave)
    simp only [execStmt, bind_assoc, pure_bind, prepareReturn]
    refine SimG.bind ((claims n).expr expr hok le ls id middle pt cfg env cx fr
      hexpr hpp hextMiddle hrel) fun value ptMiddle frMiddle hpost => ?_
    have hsim := leaveTo_sim cfg env cx le 0 middle unwound u ptMiddle frMiddle
      hpost.rel hleave hpost.pp hextUnwound
    simp only [Nat.sub_zero, List.take_length, List.drop_length] at hsim
    refine SimG.bind hsim fun _ pt' fr' hunwind => ?_
    obtain ⟨_, _, _, hinst⟩ := emitTerm_facts hterm hunwind.pp hext
    have hcell : fr'.vals[id]? = some (.val value) := by
      rw [hunwind.values]
      exact hpost.has (id, _) (by simp)
    exact SimG.ret ⟨value, rfl, ⟨⟨[id], hinst, Or.inr ⟨id, rfl, hcell⟩⟩, hunwind.scopes⟩⟩

theorem stmt_ret_prepared_sim (n : Nat) (lc : Option LoopCtx) (expr : Option Expr) (org : OriginId)
    (hok : (match expr with | none => true | some e => exprOk e) = true)
    (le : LEnv) (ls ls' : LS) (r : Unit) (pt : Pt) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (fr : GIR.Frame) (hlow : lowerStmt lc (.ret expr org) le ls = (r, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls) :
    SimG cx pt fr (execStmt n cfg env (.ret expr org) >>= prepareReturn env)
      (fun flow pt' fr' => ∃ value, flow = .ret value ∧ ReturnSite cx pt' fr' value org) := by
  cases expr with
  | none =>
    exact (stmt_ret_none_prepared n lc org le ls ls' r pt cfg env cx fr
      hlow hpp hext hrel).mono (fun _ _ _ h => ⟨.unit, h.1, h.2⟩)
  | some expr =>
    exact stmt_ret_some_prepared n lc expr org hok le ls ls' r pt cfg env cx fr
      hlow hpp hext hrel

theorem stmt_ret_prepared_correct (n : Nat) (lc : Option LoopCtx) (expr : Option Expr) (org : OriginId)
    (hok : (match expr with | none => true | some e => exprOk e) = true)
    (le : LEnv) (ls ls' : LS) (r : Unit) (pt : Pt) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (fr : GIR.Frame) (hlow : lowerStmt lc (.ret expr org) le ls = (r, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (state after : St) (value : Val)
    (hdone : (execStmt n cfg env (.ret expr org) >>= prepareReturn env) state = .ok (.ret value) after) :
    ∃ fuel, ∀ extra, runAt cx pt fr (extra + fuel) state = .ok value after := by
  have hsim := stmt_ret_prepared_sim n lc expr org hok le ls ls' r pt cfg env cx fr
    hlow hpp hext hrel
  obtain ⟨pt', fr', steps, ⟨returned, hvalue, hsite⟩, hrun⟩ := (hsim state).1 (.ret value) after hdone
  have heq : value = returned := Flow.ret.inj hvalue
  subst returned
  refine ⟨steps + 1, fun extra => ?_⟩
  rw [show extra + (steps + 1) = (extra + 1) + steps by omega, hrun (extra + 1)]
  exact hsite.run after extra

end Goose.Lower
