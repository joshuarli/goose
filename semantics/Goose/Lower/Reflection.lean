import Goose.Lower.RuntimeSim
import Goose.Proofs.Safety

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

def ReflectMFuel (fuel : Nat) (source target : Nat → M α) (state : St) : Prop :=
  ∀ result, NonTimeout result → target fuel state = result →
    ∃ sourceFuel, source sourceFuel state = result

def ReflectM (source target : Nat → M α) (state : St) : Prop :=
  ∀ fuel, ReflectMFuel fuel source target state

def FuelMonotone (source : Nat → M α) : Prop :=
  ∀ n k, n ≤ k → MonoM (source n) (source k)

def ReflectAtFuel (fuel : Nat) (cx : FnCtx) (pt : Pt) (fr : GIR.Frame) (source : Nat → M α)
    (post : α → St → Pt → GIR.Frame → Prop) (state : St) : Prop :=
  ∀ result, NonTimeout result → runAt cx pt fr fuel state = result →
    (∃ n value after pt' fr' residual,
      source n state = .ok value after ∧ post value after pt' fr' ∧
      residual ≤ fuel ∧ runAt cx pt' fr' residual after = result) ∨
    (∃ n stop after, source n state = .stop stop after ∧ result = .stop stop after)

def ReflectAt (cx : FnCtx) (pt : Pt) (fr : GIR.Frame) (source : Nat → M α)
    (post : α → St → Pt → GIR.Frame → Prop) (state : St) : Prop :=
  ∀ fuel, ReflectAtFuel fuel cx pt fr source post state

theorem ReflectM.refl (source : Nat → M α) (state : St) : ReflectM source source state :=
  fun fuel _ _ h => ⟨fuel,h⟩

theorem ReflectM.trans {source middle target : Nat → M α} {state : St}
    (left : ReflectM source middle state) (right : ReflectM middle target state) :
    ReflectM source target state := by
  intro fuel result hresult htarget
  obtain ⟨middleFuel,hmiddle⟩ := right fuel result hresult htarget
  exact left middleFuel result hresult hmiddle

theorem ReflectM.bind {source₁ target₁ : Nat → M α}
    {source₂ target₂ : α → Nat → M β} {state : St}
    (first : ReflectM source₁ target₁ state)
    (second : ∀ value after, ReflectM (source₂ value) (target₂ value) after)
    (mono₁ : FuelMonotone source₁)
    (mono₂ : ∀ value, FuelMonotone (source₂ value)) :
    ReflectM (fun n => source₁ n >>= fun value => source₂ value n)
      (fun n => target₁ n >>= fun value => target₂ value n) state := by
  intro fuel result hresult htarget
  change (target₁ fuel >>= fun value => target₂ value fuel) state = result at htarget
  change ∃ n, (source₁ n >>= fun value => source₂ value n) state = result
  rw [bind_apply] at htarget
  cases hfirst : target₁ fuel state with
  | ok value after =>
      rw [hfirst] at htarget
      obtain ⟨n,hn⟩ := first fuel (.ok value after) (NonTimeout.ok value after) hfirst
      obtain ⟨k,hk⟩ := second value after fuel result hresult htarget
      refine ⟨max n k, ?_⟩
      change (source₁ (max n k) >>= fun value => source₂ value (max n k)) state = _
      rw [bind_apply, (mono₁ n (max n k) (Nat.le_max_left _ _) state).1 value after hn]
      cases result with
      | ok value' after' => exact (mono₂ value k (max n k) (Nat.le_max_right _ _) after).1 value' after' hk
      | stop stop after' =>
          exact ((mono₂ value k (max n k) (Nat.le_max_right _ _) after).2 stop after' hk).resolve_left
            (by cases stop <;> simp [isTimeout] at *; exact (hresult after' rfl).elim)
  | stop stop after =>
      rw [hfirst] at htarget
      have hnon : NonTimeout (Res.stop stop after : Res α) := by
        intro s h
        cases h
        exact hresult after htarget.symm
      obtain ⟨n,hn⟩ := first fuel (.stop stop after) hnon hfirst
      refine ⟨n, ?_⟩
      rw [bind_apply, hn]
      exact htarget

theorem ReflectM.safe {source target : Nat → M α} {state : St}
    (reflection : ReflectM source target state)
    (safeSource : ∀ n, Core.Sound.Sat (source n) state (fun _ _ => True)) :
    ∀ n, Core.Sound.Sat (target n) state (fun _ _ => True) := by
  intro n
  cases htarget : target n state with
  | ok value after => simp [Core.Sound.Sat, htarget]
  | stop stop after =>
      cases stop with
      | fault kind =>
          obtain ⟨k,hk⟩ := reflection n (.stop (.fault kind) after)
            (by intro s h; cases h) htarget
          have hs := safeSource k
          simp [Core.Sound.Sat, hk] at hs
      | abort kind origin => simp [Core.Sound.Sat, htarget]
      | exit code => simp [Core.Sound.Sat, htarget]
      | timeout => simp [Core.Sound.Sat, htarget]

theorem ReflectAt.ret {cx : FnCtx} {pt : Pt} {fr : GIR.Frame} {value : α} {state : St}
    {post : α → St → Pt → GIR.Frame → Prop} (hpost : post value state pt fr) :
    ReflectAt cx pt fr (fun _ => pure value) post state := by
  intro fuel result hresult hrun
  exact Or.inl ⟨0,value,state,pt,fr,fuel,rfl,hpost,Nat.le_refl _,hrun⟩

theorem ReflectAt.mono {cx : FnCtx} {pt : Pt} {fr : GIR.Frame} {source : Nat → M α}
    {p q : α → St → Pt → GIR.Frame → Prop} {state : St}
    (reflection : ReflectAt cx pt fr source p state)
    (weaken : ∀ value after pt' fr', p value after pt' fr' → q value after pt' fr') :
    ReflectAt cx pt fr source q state := by
  intro fuel result hresult hrun
  rcases reflection fuel result hresult hrun with h | h
  · obtain ⟨n,value,after,pt',fr',residual,hn,hp,hle,hr⟩ := h
    exact Or.inl ⟨n,value,after,pt',fr',residual,hn,weaken _ _ _ _ hp,hle,hr⟩
  · exact Or.inr h

theorem ReflectAt.bind {cx : FnCtx} {pt : Pt} {fr : GIR.Frame}
    {source₁ : Nat → M α} {source₂ : α → Nat → M β}
    {p : α → St → Pt → GIR.Frame → Prop} {q : β → St → Pt → GIR.Frame → Prop} {state : St}
    (first : ReflectAt cx pt fr source₁ p state)
    (second : ∀ n value after pt' fr', source₁ n state = .ok value after →
      p value after pt' fr' → ReflectAt cx pt' fr' (source₂ value) q after)
    (mono₁ : FuelMonotone source₁)
    (mono₂ : ∀ value, FuelMonotone (source₂ value)) :
    ReflectAt cx pt fr (fun n => source₁ n >>= fun value => source₂ value n) q state := by
  intro fuel result hresult hrun
  rcases first fuel result hresult hrun with h | h
  · obtain ⟨n,value,after,pt',fr',residual,hn,hp,hle,hr⟩ := h
    rcases second n value after pt' fr' hn hp residual result hresult hr with h | h
    · obtain ⟨k,value',after',pt'',fr'',residual',hk,hq,hle',hr'⟩ := h
      refine Or.inl ⟨max n k,value',after',pt'',fr'',residual',?_,hq,Nat.le_trans hle' hle,hr'⟩
      change (source₁ (max n k) >>= fun value => source₂ value (max n k)) state = _
      rw [bind_apply, (mono₁ n (max n k) (Nat.le_max_left _ _) state).1 value after hn]
      exact (mono₂ value k (max n k) (Nat.le_max_right _ _) after).1 value' after' hk
    · obtain ⟨k,stop,after',hk,hr'⟩ := h
      refine Or.inr ⟨max n k,stop,after',?_,hr'⟩
      change (source₁ (max n k) >>= fun value => source₂ value (max n k)) state = _
      rw [bind_apply, (mono₁ n (max n k) (Nat.le_max_left _ _) state).1 value after hn]
      exact ((mono₂ value k (max n k) (Nat.le_max_right _ _) after).2 stop after' hk).resolve_left
        (by cases stop <;> simp [isTimeout] at *; exact (hresult after' hr').elim)
  · obtain ⟨n,stop,after,hn,hr⟩ := h
    refine Or.inr ⟨n,stop,after,?_,hr⟩
    change (source₁ n >>= fun value => source₂ value n) state = _
    rw [bind_apply, hn]

theorem reflected_lowering_never_faults {module : Core.Module}
    (accepted : Core.validate module = .ok ()) (profile : NumProfile)
    (reflection : ReflectM (fun n => Core.runModule n ⟨profile,module⟩)
      (fun n => GIR.runModule n ⟨profile,lower module⟩) St.initial) :
    ∀ fuel kind, GIR.run fuel profile (lower module) ≠ .fault kind := by
  intro fuel kind htarget
  unfold GIR.run at htarget
  cases hr : GIR.runModule fuel ⟨profile,lower module⟩ St.initial with
  | ok value after => simp [hr] at htarget
  | stop stop after =>
      cases stop with
      | fault faultKind =>
          obtain ⟨n,hn⟩ := reflection fuel (.stop (.fault faultKind) after)
            (by intro s h; cases h) hr
          have hs := Goose.Proofs.Safety.validated_never_faults module accepted n profile faultKind
          apply hs
          simp [Core.eval, hn]
      | abort kind origin => simp [hr] at htarget
      | exit code => simp [hr] at htarget
      | timeout => simp [hr] at htarget

end Goose.Lower
