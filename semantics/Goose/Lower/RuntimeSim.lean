import Goose.Lower.Eventual

namespace Goose.Lower

open Goose.Core Goose.GIR

def SimEAt (cx : FnCtx) (pt : Pt) (fr : Frame) (c : M α)
    (post : α → Pt → Frame → Prop) (s : St) : Prop :=
  (∀ a s1, c s = .ok a s1 →
    ∃ pt' fr', post a pt' fr' ∧ ∀ j result, NonTimeout result →
      runAt cx pt' fr' j s1 = result → ∃ K, ∀ k, K ≤ k → runAt cx pt fr k s = result) ∧
  (∀ e s1, c s = .stop e s1 → IsFinal e →
    ∃ K, ∀ k, K ≤ k → runAt cx pt fr k s = .stop e s1)

def SimEOn (cx : FnCtx) (pt : Pt) (fr : Frame) (c : M α)
    (post : α → Pt → Frame → Prop) (allowed : St → Prop) : Prop :=
  ∀ s, allowed s → SimEAt cx pt fr c post s

theorem SimE.at_state {cx : FnCtx} {pt : Pt} {fr : Frame} {c : M α}
    {post : α → Pt → Frame → Prop} (h : SimE cx pt fr c post) (s : St) :
    SimEAt cx pt fr c post s := h s

theorem SimE.on_states {cx : FnCtx} {pt : Pt} {fr : Frame} {c : M α}
    {post : α → Pt → Frame → Prop} (h : SimE cx pt fr c post) (allowed : St → Prop) :
    SimEOn cx pt fr c post allowed := fun s _ => h.at_state s

theorem SimEAt.of_simG {cx : FnCtx} {pt : Pt} {fr : Frame} {c : M α}
    {post : α → Pt → Frame → Prop} (h : SimG cx pt fr c post) (s : St) :
    SimEAt cx pt fr c post s := (SimE.of_simG h).at_state s

theorem SimEAt.ret {cx : FnCtx} {pt : Pt} {fr : Frame} {a : α}
    {post : α → Pt → Frame → Prop} {s : St} (h : post a pt fr) :
    SimEAt cx pt fr (Pure.pure a : M α) post s := (SimE.ret h).at_state s

theorem SimEAt.mono {cx : FnCtx} {pt : Pt} {fr : Frame} {c : M α} {s : St}
    {p q : α → Pt → Frame → Prop} (h : SimEAt cx pt fr c p s)
    (hpq : ∀ a s1 pt' fr', c s = .ok a s1 → p a pt' fr' → q a pt' fr') :
    SimEAt cx pt fr c q s := by
  refine ⟨fun a s1 hc => ?_, h.2⟩
  obtain ⟨pt', fr', hp, he⟩ := h.1 a s1 hc
  exact ⟨pt', fr', hpq a s1 pt' fr' hc hp, he⟩

theorem SimEAt.bind {cx : FnCtx} {pt : Pt} {fr : Frame} {c1 : M α} {s : St}
    {p1 : α → Pt → Frame → Prop} {c2 : α → M β} {p2 : β → Pt → Frame → Prop}
    (h1 : SimEAt cx pt fr c1 p1 s)
    (h2 : ∀ a s1 pt1 fr1, c1 s = .ok a s1 → p1 a pt1 fr1 →
      SimEAt cx pt1 fr1 (c2 a) p2 s1) :
    SimEAt cx pt fr (c1 >>= c2) p2 s := by
  refine ⟨?_, ?_⟩
  · intro b s2 hc
    rw [bind_apply] at hc
    cases hc1 : c1 s with
    | stop e s1 => rw [hc1] at hc; cases hc
    | ok a s1 =>
      rw [hc1] at hc
      obtain ⟨pt1, fr1, hp1, he1⟩ := h1.1 a s1 hc1
      obtain ⟨pt2, fr2, hp2, he2⟩ := (h2 a s1 pt1 fr1 hc1 hp1).1 b s2 hc
      refine ⟨pt2, fr2, hp2, fun j result hf hr => ?_⟩
      obtain ⟨K, hK⟩ := he2 j result hf hr
      exact he1 K result hf (hK K (Nat.le_refl K))
  · intro e s2 hc hf
    rw [bind_apply] at hc
    cases hc1 : c1 s with
    | stop e1 s1 => rw [hc1] at hc; cases hc; exact h1.2 e s2 hc1 hf
    | ok a s1 =>
      rw [hc1] at hc
      obtain ⟨pt1, fr1, hp1, he1⟩ := h1.1 a s1 hc1
      obtain ⟨K, hK⟩ := (h2 a s1 pt1 fr1 hc1 hp1).2 e s2 hc hf
      exact he1 K (.stop e s2) (NonTimeout.final hf s2) (hK K (Nat.le_refl K))

theorem SimEAt.goes {cx : FnCtx} {pt pt1 : Pt} {fr fr1 : Frame} {c : M α}
    {post : α → Pt → Frame → Prop} {s : St} (hg : Goes cx pt fr pt1 fr1)
    (h : SimEAt cx pt1 fr1 c post s) : SimEAt cx pt fr c post s := by
  obtain ⟨d, hd⟩ := hg
  refine ⟨?_, ?_⟩
  · intro a s1 hc
    obtain ⟨pt', fr', hp, he⟩ := h.1 a s1 hc
    refine ⟨pt', fr', hp, fun j result hf hr => ?_⟩
    obtain ⟨K, hK⟩ := he j result hf hr
    refine ⟨K + d, fun k hk => ?_⟩
    obtain ⟨l, rfl⟩ : ∃ l, k = l + d := ⟨k - d, by omega⟩
    rw [hd l]
    exact hK l (by omega)
  · intro e s1 hc hf
    obtain ⟨K, hK⟩ := h.2 e s1 hc hf
    refine ⟨K + d, fun k hk => ?_⟩
    obtain ⟨l, rfl⟩ : ∃ l, k = l + d := ⟨k - d, by omega⟩
    rw [hd l]
    exact hK l (by omega)

theorem SimEAt.mono_goes {cx : FnCtx} {pt : Pt} {fr : Frame} {c : M α} {s : St}
    {p q : α → Pt → Frame → Prop} (h : SimEAt cx pt fr c p s)
    (hq : ∀ a s1 pt' fr', c s = .ok a s1 → p a pt' fr' →
      ∃ pt'' fr'', Goes cx pt' fr' pt'' fr'' ∧ q a pt'' fr'') :
    SimEAt cx pt fr c q s := by
  refine ⟨fun a s1 hc => ?_, h.2⟩
  obtain ⟨pt', fr', hp, he⟩ := h.1 a s1 hc
  obtain ⟨pt'', fr'', ⟨d, hd⟩, hq'⟩ := hq a s1 pt' fr' hc hp
  refine ⟨pt'', fr'', hq', fun j result hf hr => ?_⟩
  exact he (j + d) result hf ((congrFun (hd j) s1).trans hr)

theorem SimEAt.def_step {cx : FnCtx} {pt : Pt} {fr : Frame} {r : ValueId} {op : Op}
    {c : M α} {s : St} (inj : α → RVal) (hi : instAt cx.fn pt = some (.def r op))
    (hx : EventualM (c >>= fun a => pure (inj a)) (fun k => execOp k cx fr op) s) :
    SimEAt cx pt fr c
      (fun a pt' fr' => pt' = (pt.1, pt.2 + 1) ∧ fr' = fr.set r (inj a)) s := by
  have key : ∀ k, runAt cx pt fr (k + 1) =
      (execOp k cx fr op >>= fun x => runAt cx (pt.1, pt.2 + 1) (fr.set r x) k) := by
    intro k
    unfold runAt
    rw [instsAt_cons hi, exec]
    simp only [setCell_eq, pure_bind]
  refine ⟨?_, ?_⟩
  · intro a s1 hc
    have hc' : (c >>= fun a => pure (inj a)) s = .ok (inj a) s1 := by
      simp only [bind_apply, hc, pure_apply]
    obtain ⟨K, hK⟩ := hx.1 (inj a) s1 hc'
    refine ⟨(pt.1, pt.2 + 1), fr.set r (inj a), ⟨rfl, rfl⟩,
      fun j result hf hr => ⟨max K j + 1, fun k hk => ?_⟩⟩
    obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
    simp only [key l, bind_apply, hK l (by omega)]
    exact runAt_fuel_mono (by omega) cx _ _ s1 hf hr
  · intro e s1 hc hf
    have hc' : (c >>= fun a => pure (inj a)) s = .stop e s1 := by
      rw [bind_apply, hc]
    obtain ⟨K, hK⟩ := hx.2 e s1 hc' hf
    refine ⟨K + 1, fun k hk => ?_⟩
    obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
    simp only [key l, bind_apply, hK l (by omega)]

theorem SimEAt.of_stops {cx : FnCtx} {pt : Pt} {fr : Frame} {c : M α} {c' : M β}
    {p : α → Pt → Frame → Prop} {q : β → Pt → Frame → Prop} {s : St}
    (hn : ∀ b s1, c' s ≠ .ok b s1) (hst : ∀ e s1, c' s = .stop e s1 → c s = .stop e s1)
    (h : SimEAt cx pt fr c p s) : SimEAt cx pt fr c' q s :=
  ⟨fun b s1 hc => absurd hc (hn b s1), fun e s1 hc hf => h.2 e s1 (hst e s1 hc) hf⟩

theorem SimEAt.of_timeout {cx : FnCtx} {pt : Pt} {fr : Frame}
    {p : α → Pt → Frame → Prop} (s : St) :
    SimEAt cx pt fr (Goose.Core.timeout : M α) p s := SimE.of_timeout.at_state s

theorem SimEAt.expectBool {cx : FnCtx} {pt : Pt} {fr : Frame} {value : Val}
    {next : Bool → M α} {post : α → Pt → Frame → Prop} {state : St}
    (h : ∀ branch, value = .bool branch → SimEAt cx pt fr (next branch) post state) :
    SimEAt cx pt fr (Core.expectBool value >>= next) post state := by
  cases value with
  | bool branch => exact h branch rfl
  | _ => exact SimEAt.of_simG (SimG.of_fault_bind fun s => ⟨_, s, rfl⟩) state

theorem SimEAt.expectInt {cx : FnCtx} {pt : Pt} {fr : Frame} {value : Val}
    {next : IntTy × Int → M α} {post : α → Pt → Frame → Prop} {state : St}
    (h : ∀ ty number, value = .int ty number →
      SimEAt cx pt fr (next (ty, number)) post state) :
    SimEAt cx pt fr (Core.expectInt value >>= next) post state := by
  cases value with
  | int ty number => exact h ty number rfl
  | _ => exact SimEAt.of_simG (SimG.of_fault_bind fun s => ⟨_, s, rfl⟩) state

theorem SimEOn.at_state {cx : FnCtx} {pt : Pt} {fr : Frame} {c : M α}
    {post : α → Pt → Frame → Prop} {allowed : St → Prop}
    (h : SimEOn cx pt fr c post allowed) {s : St} (hs : allowed s) :
    SimEAt cx pt fr c post s := h s hs

theorem SimEOn.restrict {cx : FnCtx} {pt : Pt} {fr : Frame} {c : M α}
    {post : α → Pt → Frame → Prop} {allowed narrower : St → Prop}
    (h : SimEOn cx pt fr c post allowed) (hn : ∀ s, narrower s → allowed s) :
    SimEOn cx pt fr c post narrower := fun s hs => h s (hn s hs)

theorem SimEOn.bind {cx : FnCtx} {pt : Pt} {fr : Frame} {c1 : M α}
    {p1 : α → Pt → Frame → Prop} {c2 : α → M β} {p2 : β → Pt → Frame → Prop}
    {allowed : St → Prop} (h1 : SimEOn cx pt fr c1 p1 allowed)
    (h2 : ∀ s, allowed s → ∀ a s1 pt1 fr1, c1 s = .ok a s1 → p1 a pt1 fr1 →
      SimEAt cx pt1 fr1 (c2 a) p2 s1) :
    SimEOn cx pt fr (c1 >>= c2) p2 allowed :=
  fun s hs => (h1 s hs).bind (h2 s hs)

end Goose.Lower
