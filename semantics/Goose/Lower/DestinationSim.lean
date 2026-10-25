import Goose.Lower.Coerce
import Goose.Lower.ReturnState

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem coerceSlot_eq {le : LEnv} {slot : SlotId} {destination : Slot}
    (h : le.slots[slot]? = some destination) (value : ValueId) (org : OriginId) :
    coerceSlot slot value org le = coerceTo destination.ty value org le := by
  funext ls
  simp only [coerceSlot, bind_run, read_apply, h]

theorem coerceResult_eq {le : LEnv} {destination : Ty}
    (h : le.results.head? = some destination) (value : ValueId) (org : OriginId) :
    coerceResult value org le = coerceTo destination value org le := by
  funext ls
  simp only [coerceResult, bind_run, read_apply, h]

theorem stmt_let_coerced_at {n : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx}
    {le : LEnv} {slot : SlotId} {expr : Expr} {org : OriginId}
    {ls middle casted ls' : LS} {id result : ValueId} {pt : Pt} {fr : GIR.Frame} {state : St}
    {destination : Slot}
    (hslot : le.slots[slot]? = some destination)
    (hvalue : lowerExpr expr le ls = (id, middle))
    (hcast : coerceSlot slot id org le middle = (result, casted))
    (heffect : emitEffect (.slotInit slot result (some org)) le casted = ((), ls'))
    (hext : ExtT ls' cx.fn.blocks)
    (hexpr : SimEAt cx pt fr (evalExpr n cfg env expr)
      (fun value pt' fr' => Post cfg env cx ls fr middle fr' pt' [(id, .val value)]) state)
    (hshape : ∀ value after, evalExpr n cfg env expr state = .ok value after →
      CoercionValue destination.ty value) :
    SimEAt cx pt fr (execStmt (n + 1) cfg env (.letS slot expr org))
      (fun flow pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' []) state := by
  have hextCast := hext.of_adv (adv_emitEffect heffect)
  rw [coerceSlot_eq hslot id org] at hcast
  simp only [execStmt]
  refine SimEAt.bind hexpr fun value after pt1 fr1 hdone P => ?_
  show SimEAt cx pt1 fr1 ((pure value : M Val) >>= fun value =>
    rootOf env slot >>= fun root => bindRoot root value >>= fun _ => pure (Flow.normal .unit)) _ after
  refine SimEAt.bind ((coerceTo_sim P (hshape value after hdone) hcast hextCast).at_state after)
    fun coerced afterCast pt2 fr2 hcastDone hpost => ?_
  obtain ⟨hcoerced, Q⟩ := hpost
  subst coerced
  have hcell := Q.has (result, .val value) (by simp)
  have heff : execEff cx.fn fr2 (.slotInit slot result (some org)) =
      (rootOf env slot >>= fun root => bindRoot root value) >>= fun _ => pure fr2 := by
    simp only [execEff, slotRoot_eq Q.rel, getVal_of hcell, bind_assoc, pure_bind]
  exact SimEAt.of_simG (leaf_eff Q heffect hext (Flow.normal .unit)
    (by simp only [bind_assoc]) heff) afterCast

theorem stmt_let_coerced_sim {n : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx}
    {le : LEnv} {loop : Option LoopCtx} {slot : SlotId} {expr : Expr} {org : OriginId}
    {ls ls' : LS} {pt : Pt} {fr : GIR.Frame} {state : St} {destination : Slot}
    (hslot : le.slots[slot]? = some destination)
    (hlow : lowerStmt loop (.letS slot expr org) le ls = ((), ls'))
    (hext : ExtT ls' cx.fn.blocks)
    (hexpr : ∀ id middle, lowerExpr expr le ls = (id, middle) → ExtT middle cx.fn.blocks →
      SimEAt cx pt fr (evalExpr n cfg env expr)
        (fun value pt' fr' => Post cfg env cx ls fr middle fr' pt' [(id, .val value)]) state)
    (hshape : ∀ value after, evalExpr n cfg env expr state = .ok value after →
      CoercionValue destination.ty value) :
    SimEAt cx pt fr (execStmt (n + 1) cfg env (.letS slot expr org))
      (fun flow pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' []) state := by
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨id, middle, hvalue, result, casted, hcast, heffect⟩ := hlow
  have hextCast := hext.of_adv (adv_emitEffect heffect)
  have hextMiddle := hextCast.of_adv (advB_coerceSlot slot id org _ _ _ _ hcast)
  exact stmt_let_coerced_at hslot hvalue hcast heffect hext
    (hexpr id middle hvalue hextMiddle) hshape

theorem stmt_rebind_coerced_sim {n : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx}
    {le : LEnv} {loop : Option LoopCtx} {slot : SlotId} {expr : Expr} {org : OriginId}
    {ls ls' : LS} {pt : Pt} {fr : GIR.Frame} {state : St} {destination : Slot}
    (hslot : le.slots[slot]? = some destination)
    (hlow : lowerStmt loop (.rebind slot expr org) le ls = ((), ls'))
    (hext : ExtT ls' cx.fn.blocks)
    (hexpr : ∀ id middle, lowerExpr expr le ls = (id, middle) → ExtT middle cx.fn.blocks →
      SimEAt cx pt fr (evalExpr n cfg env expr)
        (fun value pt' fr' => Post cfg env cx ls fr middle fr' pt' [(id, .val value)]) state)
    (hshape : ∀ value after, evalExpr n cfg env expr state = .ok value after →
      CoercionValue destination.ty value) :
    SimEAt cx pt fr (execStmt (n + 1) cfg env (.rebind slot expr org))
      (fun flow pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' []) state := by
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨id, middle, hvalue, result, casted, hcast, addr, addressed, haddress, heffect⟩ := hlow
  have hextAddressed := hext.of_adv (adv_emitEffect heffect)
  have hextCast := hextAddressed.of_adv (adv_emitDef haddress)
  have hextMiddle := hextCast.of_adv (advB_coerceSlot slot id org _ _ _ _ hcast)
  rw [coerceSlot_eq hslot id org] at hcast
  simp only [execStmt]
  refine SimEAt.bind (hexpr id middle hvalue hextMiddle)
    fun value after pt1 fr1 hdone P => ?_
  show SimEAt cx pt1 fr1 ((pure value : M Val) >>= fun value =>
    rootOf env slot >>= fun root => writeLoc ⟨root, []⟩ value >>= fun _ => pure (Flow.normal .unit)) _ after
  refine SimEAt.bind ((coerceTo_sim P (hshape value after hdone) hcast hextCast).at_state after)
    fun coerced afterCast pt2 fr2 hcastDone hpost => ?_
  obtain ⟨hcoerced, Q⟩ := hpost
  subst coerced
  rw [show (rootOf env slot >>= fun root => writeLoc ⟨root, []⟩ value >>= fun _ =>
      pure (Flow.normal .unit)) =
    ((rootOf env slot >>= fun root => pure (Loc.mk root [])) >>= fun location =>
      writeLoc location value >>= fun _ => pure (Flow.normal .unit)) by simp [bind_assoc]]
  refine SimEAt.bind (SimEAt.of_simG (leaf_def_keep Q haddress hextAddressed (by simp)
    (fun location => RVal.val (.ref location)) (by
      simp only [execPure, slotRoot_eq Q.rel, bind_assoc, pure_bind])) afterCast)
    fun location afterAddress pt3 fr3 haddressDone R => ?_
  have haddr := R.has (addr, .val (.ref location)) (by simp)
  have hcell := R.has (result, .val value) (by simp)
  have heff : execEff cx.fn fr3 (.store addr result (some org)) =
      writeLoc location value >>= fun _ => pure fr3 := by
    simp only [execEff, getVal_of haddr, getVal_of hcell, Goose.Core.expectRef, bind_assoc, pure_bind]
  exact SimEAt.of_simG (leaf_eff R heffect hext (Flow.normal .unit) rfl heff) afterAddress

theorem stmt_ret_coerced_sim {n : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx}
    {le : LEnv} {loop : Option LoopCtx} {expr : Expr} {org : OriginId}
    {ls ls' : LS} {pt : Pt} {fr : GIR.Frame} {state : St} {destination : Ty}
    (hresult : le.results.head? = some destination)
    (hlow : lowerStmt loop (.ret (some expr) org) le ls = ((), ls'))
    (hext : ExtT ls' cx.fn.blocks)
    (hexpr : ∀ id middle, lowerExpr expr le ls = (id, middle) → ExtT middle cx.fn.blocks →
      SimEAt cx pt fr (evalExpr n cfg env expr)
        (fun value pt' fr' => Post cfg env cx ls fr middle fr' pt' [(id, .val value)]) state)
    (hshape : ∀ value after, evalExpr n cfg env expr state = .ok value after →
      CoercionValue destination value) :
    SimEAt cx pt fr (execStmt (n + 1) cfg env (.ret (some expr) org) >>= prepareReturn env)
      (fun flow pt' fr' => ∃ value, flow = .ret value ∧ ReturnSite cx pt' fr' value org) state := by
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨id, middle, hvalue, result, casted, hcast, ids, same, hpure,
    u, unwound, hleave, hterm⟩ := hlow
  rw [pure_run] at hpure
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpure
  have hextUnwound := hext.of_adv (adv_emitTerm hterm)
  have hextCast := hextUnwound.of_adv (advB_leaveTo 0 _ _ _ _ hleave)
  have hextMiddle := hextCast.of_adv (advB_coerceResult id org _ _ _ _ hcast)
  rw [coerceResult_eq hresult id org] at hcast
  simp only [execStmt, bind_assoc, pure_bind, prepareReturn]
  refine SimEAt.bind (hexpr id middle hvalue hextMiddle)
    fun value after pt1 fr1 hdone P => ?_
  show SimEAt cx pt1 fr1 ((pure value : M Val) >>= fun value =>
    releaseScopes env env.scopes >>= fun _ => pure (Flow.ret value)) _ after
  refine SimEAt.bind ((coerceTo_sim P (hshape value after hdone) hcast hextCast).at_state after)
    fun coerced afterCast pt2 fr2 hcastDone hpost => ?_
  obtain ⟨hcoerced, Q⟩ := hpost
  subst coerced
  have hsim := leaveTo_sim cfg env cx le 0 casted unwound u pt2 fr2
    Q.rel hleave Q.pp hextUnwound
  simp only [Nat.sub_zero, List.take_length, List.drop_length] at hsim
  refine SimEAt.bind (SimEAt.of_simG hsim afterCast)
    fun _ afterLeave pt3 fr3 hleaveDone hunwind => ?_
  obtain ⟨_, _, _, hinst⟩ := emitTerm_facts hterm hunwind.pp hext
  have hcell : fr3.vals[result]? = some (.val value) := by
    rw [hunwind.values]
    exact Q.has (result, _) (by simp)
  exact SimEAt.ret ⟨value, rfl, ⟨⟨[result], hinst, Or.inr ⟨result, rfl, hcell⟩⟩,
    hunwind.scopes⟩⟩

end Goose.Lower
