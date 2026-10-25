import Goose.Lower.ReflectionEffects
import Goose.Lower.GeneratedBuilder
import Goose.Lower.TypedBlocks

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

theorem block_enter_reflectAtFuel {cfg : Cfg} {env : Env} {cx : FnCtx} {ls ls1 : LS}
    {fr : Frame} {pt : Pt} {le : LEnv} {sc : ScopeId} (fuel : Nat) (state : St)
    (hpp : ls.pp = some pt) (h : emitEffect (.enter sc) le ls = ((), ls1))
    (hext : ExtT ls1 cx.fn.blocks) (hrel : Rel cfg env cx fr ls) :
    ReflectAtFuel fuel cx pt fr (fun _ => freshScope) (fun si _ pt1 fr1 =>
      ls1.pp = some pt1 ∧ ls1.vals.size = ls.vals.size ∧ fr1.vals = fr.vals ∧
      Rel cfg { env with scopes := (sc, si) :: env.scopes } cx fr1
        { ls1 with stack := sc :: ls1.stack }) state := by
  cases fuel with
  | zero => exact ReflectAtFuel.zero _ _ _ _ _ _
  | succ fuel =>
    obtain ⟨hv,hst,hpp1,hi⟩ := emitEffect_facts h hpp hext
    have equal : execEff cx.fn fr (.enter sc) = freshScope >>= fun si =>
        pure ({ fr with scopes := (sc,si) :: fr.scopes } : Frame) := rfl
    refine (ReflectAtFuel.eff_step (source := fun _ => freshScope) (sourceFuel := 0) hi equal).mono ?_
    rintro si after pt1 fr1 ⟨rfl,rfl⟩
    exact ⟨hpp1,hv,rfl,hrel.prof,hrel.slots,hrel.act,by simp [hrel.scopes],hrel.depth,
      by simp [hst,hrel.stack]⟩

theorem block_leave_reflectAtFuel {cfg : Cfg} {env : Env} {cx : FnCtx} {lsk ls_l : LS}
    {frk : Frame} {ptk : Pt} {le : LEnv} {sc : ScopeId} {si : ScopeInst}
    (fuel : Nat) (state : St) (hpp : lsk.pp = some ptk)
    (h : emitEffect (.leave sc) le lsk = ((), ls_l)) (hext : ExtT ls_l cx.fn.blocks)
    (hrel : Rel cfg { env with scopes := (sc, si) :: env.scopes } cx frk lsk) :
    ReflectAtFuel fuel cx ptk frk (fun _ => Core.releaseScope env sc si) (fun _ _ pt' fr' =>
      ls_l.pp = some pt' ∧ ls_l.vals.size = lsk.vals.size ∧ fr'.vals = frk.vals ∧
      Rel cfg env cx fr' { ls_l with stack := ls_l.stack.drop 1 }) state := by
  cases fuel with
  | zero => exact ReflectAtFuel.zero _ _ _ _ _ _
  | succ fuel =>
    obtain ⟨hv,hst,hpp1,hi⟩ := emitEffect_facts h hpp hext
    have scopes : frk.scopes = (sc,si) :: env.scopes := hrel.scopes
    have equal : execEff cx.fn frk (.leave sc) = Core.releaseScope env sc si >>= fun _ =>
        pure ({ frk with scopes := env.scopes } : Frame) := by
      simp only [execEff,scopes,↓reduceIte]
      rw [releaseScope_eq hrel sc si]
      rfl
    refine (ReflectAtFuel.eff_step (source := fun _ => Core.releaseScope env sc si)
      (sourceFuel := 0) hi equal).mono ?_
    rintro u after pt1 fr1 ⟨rfl,rfl⟩
    refine ⟨hpp1,hv,rfl,hrel.prof,hrel.slots,hrel.act,rfl,hrel.depth,?_⟩
    have stack := hrel.stack
    simp only [List.map_cons] at stack
    simp [hst,stack]

theorem initSlots_reflectAtFuel {cfg : Cfg} {env : Env} {cx : FnCtx} {sc : ScopeId} {si : ScopeInst}
    (hs : env.scopes.head? = some (sc,si)) :
    ∀ (pre : List (SlotId × ValueId × OriginId)) (pre' : List (VarId × Val)) {le : LEnv}
      {lsk ls_i : LS} {u : Unit} {ptk : Pt} {frk : Frame} (fuel : Nat) (state : St),
      (∀ p ∈ pre, ∃ lv, env.vars[p.1]? = some lv ∧ lv.scope = sc) →
      initSlots pre le lsk = (u,ls_i) → lsk.pp = some ptk → ExtT ls_i cx.fn.blocks →
      Rel cfg env cx frk lsk → PreRel frk pre pre' →
      ReflectAtFuel fuel cx ptk frk (fun _ => bindAll env.act si pre') (fun _ _ pt' fr' =>
        ls_i.pp = some pt' ∧ fr' = frk ∧ ls_i.stack = lsk.stack ∧ ls_i.vals = lsk.vals) state
  | [],[],le,lsk,ls_i,u,ptk,frk,fuel,state,_,h,hpp,hext,hrel,_ => by
    simp only [initSlots,pure_run] at h
    obtain ⟨_,rfl⟩ := Prod.mk.inj h
    exact ReflectAtFuel.ret fuel ⟨hpp,rfl,rfl,rfl⟩
  | (x,r,o) :: rest,(x',v) :: rest',le,lsk,ls_i,u,ptk,frk,fuel,state,hsc,h,hpp,hext,hrel,⟨hx,hv,hrest⟩ => by
    subst x'
    cases fuel with
    | zero => exact ReflectAtFuel.zero _ _ _ _ _ _
    | succ fuel =>
      simp only [initSlots,bind_eq] at h
      obtain ⟨u1,ls1,h1,h2⟩ := h
      have hext1 := hext.of_adv (advB_initSlots rest _ _ _ _ h2)
      obtain ⟨hv1,hst1,hpp1,hi⟩ := emitEffect_facts h1 hpp hext1
      have hvArray : ls1.vals = lsk.vals := by
        obtain ⟨blk,hc,_,_⟩ := LS.pp_some hpp
        rw [emitEffect_run _ _ hc] at h1
        obtain ⟨_,rfl⟩ := Prod.mk.inj h1
        rfl
      obtain ⟨lv,hlv,hlvs⟩ := hsc (x,r,o) (by simp)
      obtain ⟨rest0,hrest0⟩ : ∃ rest0, env.scopes = (sc,si) :: rest0 := by
        cases hh : env.scopes with
        | nil => simp [hh] at hs
        | cons hd tl => simp [hh] at hs; exact ⟨tl,by rw [hs]⟩
      have hroot := rootOf_head hrest0 hlv hlvs
      have equal : execEff cx.fn frk (.slotInit x r (some o)) =
          bindRoot (.local env.act si x) v >>= fun _ => pure frk := by
        simp only [execEff,slotRoot_eq hrel x,hroot,getVal_of hv,pure_bind]
      have first := ReflectAtFuel.eff_step (source := fun _ => bindRoot (.local env.act si x) v)
        (sourceFuel := 0) (fuel := fuel) (state := state) hi equal
      simp only [bindAll]
      refine first.bind ?_ (fun _ _ _ => MonoM.refl _) (fun _ _ _ _ => MonoM.refl _)
      intro n ignored after pt1 fr1 done matched residual bound
      obtain ⟨rfl,rfl⟩ := matched
      have rel1 := hrel.stack_eq hst1
      refine (initSlots_reflectAtFuel hs rest rest' (le := le) residual after
        (fun p hp => hsc p (by simp [hp])) h2 hpp1 hext rel1 hrest).mono ?_
      rintro a final pt' fr' ⟨point,frame,stack,values⟩
      exact ⟨point,frame,stack.trans hst1,values.trans hvArray⟩
  | [],_ :: _,_,_,_,_,_,_,_,_,_,_,_,_,_,hp => hp.elim
  | _ :: _,[],_,_,_,_,_,_,_,_,_,_,_,_,_,hp => hp.elim

end Goose.Lower
