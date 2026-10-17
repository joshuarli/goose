import Goose.Lower.Reflection

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

theorem ReflectM.map {source target : Nat → M α} {state : St}
    (reflection : ReflectM source target state) (inject : α → β) :
    ReflectM (fun n => source n >>= fun value => pure (inject value))
      (fun n => target n >>= fun value => pure (inject value)) state := by
  intro fuel result hresult htarget
  change (target fuel >>= fun value => pure (inject value)) state = result at htarget
  change ∃ n, (source n >>= fun value => pure (inject value)) state = result
  rw [bind_apply] at htarget
  cases ht : target fuel state with
  | ok value after =>
      rw [ht] at htarget
      obtain ⟨n,hn⟩ := reflection fuel (.ok value after) (NonTimeout.ok _ _) ht
      exact ⟨n,by rw [bind_apply, hn]; exact htarget⟩
  | stop stop after =>
      rw [ht] at htarget
      have hnon : NonTimeout (Res.stop stop after : Res α) := by
        intro s h
        cases h
        exact hresult after htarget.symm
      obtain ⟨n,hn⟩ := reflection fuel (.stop stop after) hnon ht
      exact ⟨n,by rw [bind_apply, hn]; exact htarget⟩

theorem ReflectAt.of_source {cx : FnCtx} {pt : Pt} {fr : GIR.Frame}
    {source other : Nat → M α} {post : α → St → Pt → GIR.Frame → Prop} {state : St}
    (reflection : ReflectAt cx pt fr source post state)
    (equal : ∀ n, ∃ k, other k state = source n state) :
    ReflectAt cx pt fr other post state := by
  intro fuel result hresult hrun
  rcases reflection fuel result hresult hrun with h | h
  · obtain ⟨n,value,after,pt',fr',residual,hn,hp,hle,hr⟩ := h
    obtain ⟨k,hk⟩ := equal n
    exact Or.inl ⟨k,value,after,pt',fr',residual,hk.trans hn,hp,hle,hr⟩
  · obtain ⟨n,stop,after,hn,hr⟩ := h
    obtain ⟨k,hk⟩ := equal n
    exact Or.inr ⟨k,stop,after,hk.trans hn,hr⟩

theorem ReflectAt.def_step {cx : FnCtx} {pt : Pt} {fr : GIR.Frame}
    {source : Nat → M α} {state : St} {resultId : ValueId} {op : Op}
    (inject : α → RVal) (instruction : instAt cx.fn pt = some (.def resultId op))
    (operation : ReflectM (fun n => source n >>= fun value => pure (inject value))
      (fun n => execOp n cx fr op) state) :
    ReflectAt cx pt fr source
      (fun value _ pt' fr' => pt' = (pt.1,pt.2 + 1) ∧ fr' = fr.set resultId (inject value)) state := by
  intro fuel result hresult hrun
  cases fuel with
  | zero => exact (hresult state (hrun.symm.trans rfl)).elim
  | succ fuel =>
      have hstep : runAt cx pt fr (fuel + 1) state =
          (execOp fuel cx fr op >>= fun value =>
            runAt cx (pt.1,pt.2 + 1) (fr.set resultId value) fuel) state := by
        simp only [runAt, instsAt_cons instruction, exec, setCell_eq, pure_bind]
      rw [hstep, bind_apply] at hrun
      cases ho : execOp fuel cx fr op state with
      | ok value after =>
          rw [ho] at hrun
          obtain ⟨n,hn⟩ := operation fuel (.ok value after) (NonTimeout.ok _ _) ho
          change (source n >>= fun value => pure (inject value)) state = .ok value after at hn
          rw [bind_apply] at hn
          cases hs : source n state with
          | stop stop stopped => rw [hs] at hn; cases hn
          | ok sourceValue sourceAfter =>
              rw [hs] at hn
              cases hn
              exact Or.inl ⟨n,sourceValue,after,(pt.1,pt.2 + 1),
                fr.set resultId (inject sourceValue),fuel,hs,⟨rfl,rfl⟩,by omega,hrun⟩
      | stop stop after =>
          rw [ho] at hrun
          have hnon : NonTimeout (Res.stop stop after : Res RVal) := by
            intro s h
            cases h
            exact hresult after hrun.symm
          obtain ⟨n,hn⟩ := operation fuel (.stop stop after) hnon ho
          change (source n >>= fun value => pure (inject value)) state = .stop stop after at hn
          rw [bind_apply] at hn
          cases hs : source n state with
          | ok sourceValue sourceAfter => rw [hs] at hn; cases hn
          | stop sourceStop sourceAfter =>
              rw [hs] at hn
              cases hn
              exact Or.inr ⟨n,stop,after,hs,hrun.symm⟩

theorem ReflectAt.goes {cx : FnCtx} {pt pt' : Pt} {fr fr' : GIR.Frame}
    {source : Nat → M α} {post : α → St → Pt → GIR.Frame → Prop} {state : St}
    (movement : Goes cx pt fr pt' fr')
    (reflection : ReflectAt cx pt' fr' source post state) :
    ReflectAt cx pt fr source post state := by
  obtain ⟨cost,hcost⟩ := movement
  intro fuel result hresult hrun
  have hlarge := runAt_fuel_mono (Nat.le_add_right fuel cost) cx pt fr state hresult hrun
  rw [hcost fuel] at hlarge
  exact reflection fuel result hresult hlarge

theorem ReflectAt.complete {cx : FnCtx} {pt : Pt} {fr : GIR.Frame}
    {source : Nat → M Val} {post : Val → St → Pt → GIR.Frame → Prop} {state : St}
    (reflection : ReflectAt cx pt fr source post state)
    (terminal : ∀ value after pt' fr', post value after pt' fr' →
      ∀ fuel result, NonTimeout result → runAt cx pt' fr' fuel after = result →
        result = .ok value after) :
    ReflectM source (fun n => runAt cx pt fr n) state := by
  intro fuel result hresult hrun
  rcases reflection fuel result hresult hrun with h | h
  · obtain ⟨n,value,after,pt',fr',residual,hn,hp,hle,hr⟩ := h
    exact ⟨n,hn.trans (terminal value after pt' fr' hp residual result hresult hr).symm⟩
  · obtain ⟨n,stop,after,hn,hr⟩ := h
    exact ⟨n,hn.trans hr.symm⟩

theorem ReflectM.call_op {cx : FnCtx} {fr : GIR.Frame} {callee : FnId}
    {args : List ValueId} {values : List Val} {origin : Option OriginId}
    {source : Nat → M Val} {state : St}
    (arguments : mapList (getVal fr) args = pure values)
    (call : ReflectM source (fun n => callFn n cx.cfg fr.depth callee values) state) :
    ReflectM (fun n => source n >>= fun value => pure (RVal.val value))
      (fun n => execOp n cx fr (.call callee args origin)) state := by
  intro fuel result hresult hrun
  cases fuel with
  | zero => exact (hresult state (hrun.symm.trans rfl)).elim
  | succ fuel =>
      have hstep : execOp (fuel + 1) cx fr (.call callee args origin) =
          (callFn fuel cx.cfg fr.depth callee values >>= fun value => pure (RVal.val value)) := by
        simp only [execOp, arguments, pure_bind]
      change execOp (fuel + 1) cx fr (.call callee args origin) state = result at hrun
      rw [hstep] at hrun
      exact call.map RVal.val fuel result hresult hrun

end Goose.Lower
