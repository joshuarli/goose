import Goose.Lower.Sim
import Goose.Proofs.GIRFuel

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

private structure FuelMono (n k : Nat) : Prop where
  call : ∀ cfg depth f vals, MonoM (callFn n cfg depth f vals) (callFn k cfg depth f vals)
  enter : ∀ cfg depth fn vals, MonoM (enterFn n cfg depth fn vals) (enterFn k cfg depth fn vals)
  exec : ∀ cx fr insts, MonoM (exec n cx fr insts) (exec k cx fr insts)
  op : ∀ cx fr instr, MonoM (execOp n cx fr instr) (execOp k cx fr instr)

private theorem op_step (n k : Nat) (ih : FuelMono n k) (cx : FnCtx) (fr : Frame) (op : Op) :
    MonoM (execOp (n + 1) cx fr op) (execOp (k + 1) cx fr op) := by
  cases op with
  | call f args org =>
    simp only [execOp]
    refine MonoM.bind (MonoM.mapList (fun _ => MonoM.refl _) args) ?_
    intro vals
    exact MonoM.bind (ih.call cx.cfg fr.depth f vals) (fun v => MonoM.refl _)
  | _ => simp only [execOp]; exact MonoM.refl _

private theorem jump_mono {n k : Nat} (ih : FuelMono n k)
    (cx : FnCtx) (fr : Frame) (b : BlockId) (args : List ValueId) :
    MonoM
      (do let vals ← mapList (getCell fr) args
          let (insts, fr') ← enterBlock cx.fn fr b vals
          exec n cx fr' insts)
      (do let vals ← mapList (getCell fr) args
          let (insts, fr') ← enterBlock cx.fn fr b vals
          exec k cx fr' insts) := by
  refine MonoM.bind (MonoM.mapList (fun _ => MonoM.refl _) args) ?_
  intro vals
  refine MonoM.bind (MonoM.refl _) ?_
  intro pair
  exact ih.exec cx pair.2 pair.1

private theorem step (n k : Nat) (ih : FuelMono n k) : FuelMono (n + 1) (k + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cfg depth f vals
    by_cases hd : depth ≥ maxCallDepth
    · simp [callFn, hd]
      exact MonoM.timeout _
    · simp only [callFn, hd, ↓reduceIte]
      exact MonoM.bind (MonoM.refl _) (fun fn => ih.enter cfg (depth + 1) fn vals)
  · intro cfg depth fn vals
    by_cases hp : fn.params.length = vals.length
    · simp only [enterFn, hp, ↓reduceIte]
      refine MonoM.bind (MonoM.refl _) ?_
      intro act
      refine MonoM.bind (MonoM.refl _) ?_
      intro pair
      exact ih.exec ⟨cfg, fn⟩ pair.2 pair.1
    · simp [enterFn, hp]
      exact MonoM.refl _
  · intro cx fr insts
    cases insts with
    | nil => simp only [exec]; exact MonoM.refl _
    | cons i rest =>
      cases i with
      | «def» r op =>
        simp only [exec]
        exact MonoM.bind (ih.op cx fr op) (fun x =>
          MonoM.bind (MonoM.refl _) (fun fr' => ih.exec cx fr' rest))
      | eff e =>
        simp only [exec]
        exact MonoM.bind (MonoM.refl _) (fun fr' => ih.exec cx fr' rest)
      | term t =>
        cases t with
        | br b args =>
          simp only [exec]
          exact jump_mono ih cx fr b args
        | condbr c tb targs eb eargs =>
          simp only [exec]
          refine MonoM.bind (MonoM.refl _) ?_
          intro value
          refine MonoM.bind (MonoM.refl _) ?_
          intro cond
          cases cond with
          | true => exact jump_mono ih cx fr tb targs
          | false => exact jump_mono ih cx fr eb eargs
        | ret vs org => simp only [exec]; exact MonoM.refl _
        | abort kind org => simp only [exec]; exact MonoM.refl _
        | exit v org => simp only [exec]; exact MonoM.refl _
        | unreachable => simp only [exec]; exact MonoM.refl _
  · intro cx fr op
    exact op_step n k ih cx fr op

private theorem zero (k : Nat) : FuelMono 0 k := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intros; simp only [callFn]; exact MonoM.timeout _
  · intros; simp only [enterFn]; exact MonoM.timeout _
  · intros; simp only [exec]; exact MonoM.timeout _
  · intro cx fr op
    cases op with
    | call f args org => simp only [execOp]; exact MonoM.timeout _
    | _ => simp only [execOp]; exact MonoM.refl _

private theorem all : ∀ (n k : Nat), n ≤ k → FuelMono n k
  | 0, k, _ => zero k
  | n + 1, 0, h => absurd h (by omega)
  | n + 1, k + 1, h => step n k (all n k (by omega))

theorem exec_fuel_mono (n k : Nat) (h : n ≤ k) (cx : FnCtx) (fr : Frame) (insts : List Inst) :
    MonoM (exec n cx fr insts) (exec k cx fr insts) := (all n k h).exec cx fr insts

theorem enterFn_fuel_mono (n k : Nat) (h : n ≤ k) (cfg : GCfg) (depth : Nat)
    (fn : Func) (vals : List Val) :
    MonoM (enterFn n cfg depth fn vals) (enterFn k cfg depth fn vals) :=
  (all n k h).enter cfg depth fn vals

theorem callFn_fuel_mono (n k : Nat) (h : n ≤ k) (cfg : GCfg) (depth : Nat)
    (f : FnId) (vals : List Val) :
    MonoM (callFn n cfg depth f vals) (callFn k cfg depth f vals) :=
  (all n k h).call cfg depth f vals

def NonTimeout (r : Res α) : Prop := ∀ s, r ≠ .stop .timeout s

theorem NonTimeout.ok (a : α) (s : St) : NonTimeout (.ok a s) := by
  intro s' h
  cases h

theorem NonTimeout.final {e : Stop} (he : IsFinal e) (s : St) : NonTimeout (Res.stop e s : Res α) := by
  intro s' h
  cases h
  exact he

theorem runAt_fuel_mono {n k : Nat} (h : n ≤ k) (cx : FnCtx) (pt : Pt) (fr : Frame)
    (s : St) {result : Res Val} (hf : NonTimeout result) (hr : runAt cx pt fr n s = result) :
    runAt cx pt fr k s = result := by
  have hm := exec_fuel_mono n k h cx fr (instsAt cx.fn pt) s
  cases result with
  | ok a s1 => exact hm.1 a s1 hr
  | stop e s1 =>
    exact (hm.2 e s1 hr).resolve_left (by
      cases e <;> simp [isTimeout] at *
      exact (hf s1 rfl).elim)

def EventualM (c : M α) (g : Nat → M α) (s : St) : Prop :=
  (∀ a s1, c s = .ok a s1 → ∃ K, ∀ k, K ≤ k → g k s = .ok a s1) ∧
  (∀ e s1, c s = .stop e s1 → IsFinal e → ∃ K, ∀ k, K ≤ k → g k s = .stop e s1)

def SimE (cx : FnCtx) (pt : Pt) (fr : Frame) (c : M α) (post : α → Pt → Frame → Prop) : Prop :=
  ∀ s, (∀ a s1, c s = .ok a s1 →
    ∃ pt' fr', post a pt' fr' ∧ ∀ j result, NonTimeout result →
      runAt cx pt' fr' j s1 = result → ∃ K, ∀ k, K ≤ k → runAt cx pt fr k s = result) ∧
    (∀ e s1, c s = .stop e s1 → IsFinal e →
      ∃ K, ∀ k, K ≤ k → runAt cx pt fr k s = .stop e s1)

theorem SimE.of_simG {cx : FnCtx} {pt : Pt} {fr : Frame} {c : M α}
    {post : α → Pt → Frame → Prop} (h : SimG cx pt fr c post) : SimE cx pt fr c post := by
  intro s
  refine ⟨?_, ?_⟩
  · intro a s1 hc
    obtain ⟨pt', fr', d, hp, hd⟩ := (h s).1 a s1 hc
    refine ⟨pt', fr', hp, fun j result hf hr => ⟨j + d, fun k hk => ?_⟩⟩
    exact runAt_fuel_mono hk cx pt fr s hf ((hd j).trans hr)
  · intro e s1 hc hf
    obtain ⟨d, hd⟩ := (h s).2 e s1 hc hf
    refine ⟨d, fun k hk => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + d := ⟨k - d, by omega⟩
    exact hd j

theorem SimE.ret {cx : FnCtx} {pt : Pt} {fr : Frame} {a : α}
    {post : α → Pt → Frame → Prop} (h : post a pt fr) :
    SimE cx pt fr (Pure.pure a : M α) post := SimE.of_simG (SimG.ret h)

theorem SimE.mono {cx : FnCtx} {pt : Pt} {fr : Frame} {c : M α}
    {p q : α → Pt → Frame → Prop} (h : SimE cx pt fr c p)
    (hpq : ∀ a pt' fr', p a pt' fr' → q a pt' fr') : SimE cx pt fr c q := by
  intro s
  refine ⟨fun a s1 hc => ?_, (h s).2⟩
  obtain ⟨pt', fr', hp, he⟩ := (h s).1 a s1 hc
  exact ⟨pt', fr', hpq a pt' fr' hp, he⟩

theorem SimE.bind {cx : FnCtx} {pt : Pt} {fr : Frame} {c1 : M α}
    {p1 : α → Pt → Frame → Prop} {c2 : α → M β} {p2 : β → Pt → Frame → Prop}
    (h1 : SimE cx pt fr c1 p1)
    (h2 : ∀ a pt1 fr1, p1 a pt1 fr1 → SimE cx pt1 fr1 (c2 a) p2) :
    SimE cx pt fr (c1 >>= c2) p2 := by
  intro s
  refine ⟨?_, ?_⟩
  · intro b s2 hc
    rw [bind_apply] at hc
    cases hc1 : c1 s with
    | stop e s1 => rw [hc1] at hc; cases hc
    | ok a s1 =>
      rw [hc1] at hc
      obtain ⟨pt1, fr1, hp1, he1⟩ := (h1 s).1 a s1 hc1
      obtain ⟨pt2, fr2, hp2, he2⟩ := ((h2 a pt1 fr1 hp1) s1).1 b s2 hc
      refine ⟨pt2, fr2, hp2, fun j result hf hr => ?_⟩
      obtain ⟨K, hK⟩ := he2 j result hf hr
      exact he1 K result hf (hK K (Nat.le_refl K))
  · intro e s2 hc hf
    rw [bind_apply] at hc
    cases hc1 : c1 s with
    | stop e1 s1 => rw [hc1] at hc; cases hc; exact (h1 s).2 e s2 hc1 hf
    | ok a s1 =>
      rw [hc1] at hc
      obtain ⟨pt1, fr1, hp1, he1⟩ := (h1 s).1 a s1 hc1
      obtain ⟨K, hK⟩ := ((h2 a pt1 fr1 hp1) s1).2 e s2 hc hf
      exact he1 K (.stop e s2) (NonTimeout.final hf s2) (hK K (Nat.le_refl K))

theorem SimE.goes {cx : FnCtx} {pt pt1 : Pt} {fr fr1 : Frame} {c : M α}
    {post : α → Pt → Frame → Prop} (hg : Goes cx pt fr pt1 fr1)
    (h : SimE cx pt1 fr1 c post) : SimE cx pt fr c post := by
  obtain ⟨d, hd⟩ := hg
  intro s
  refine ⟨?_, ?_⟩
  · intro a s1 hc
    obtain ⟨pt', fr', hp, he⟩ := (h s).1 a s1 hc
    refine ⟨pt', fr', hp, fun j result hf hr => ?_⟩
    obtain ⟨K, hK⟩ := he j result hf hr
    refine ⟨K + d, fun k hk => ?_⟩
    obtain ⟨l, rfl⟩ : ∃ l, k = l + d := ⟨k - d, by omega⟩
    rw [hd l]
    exact hK l (by omega)
  · intro e s1 hc hf
    obtain ⟨K, hK⟩ := (h s).2 e s1 hc hf
    refine ⟨K + d, fun k hk => ?_⟩
    obtain ⟨l, rfl⟩ : ∃ l, k = l + d := ⟨k - d, by omega⟩
    rw [hd l]
    exact hK l (by omega)

theorem EventualM.bind {c1 : M α} {g1 : Nat → M α} {c2 : α → M β} {g2 : α → Nat → M β} {s : St}
    (h1 : EventualM c1 g1 s) (h2 : ∀ a s1, c1 s = .ok a s1 → EventualM (c2 a) (g2 a) s1) :
    EventualM (c1 >>= c2) (fun k => g1 k >>= fun a => g2 a k) s := by
  refine ⟨fun b s2 hc => ?_, fun e s2 hc hf => ?_⟩
  · rw [bind_apply] at hc
    cases hc1 : c1 s with
    | stop e s1 => rw [hc1] at hc; cases hc
    | ok a s1 =>
      rw [hc1] at hc
      obtain ⟨K1, hK1⟩ := h1.1 a s1 hc1
      obtain ⟨K2, hK2⟩ := (h2 a s1 hc1).1 b s2 hc
      refine ⟨max K1 K2, fun k hk => ?_⟩
      show (g1 k >>= fun a => g2 a k) s = _
      rw [bind_apply, hK1 k (Nat.le_trans (Nat.le_max_left _ _) hk)]
      exact hK2 k (Nat.le_trans (Nat.le_max_right _ _) hk)
  · rw [bind_apply] at hc
    cases hc1 : c1 s with
    | stop e1 s1 =>
      rw [hc1] at hc
      cases hc
      obtain ⟨K1, hK1⟩ := h1.2 e s2 hc1 hf
      refine ⟨K1, fun k hk => ?_⟩
      show (g1 k >>= fun a => g2 a k) s = _
      rw [bind_apply, hK1 k hk]
    | ok a s1 =>
      rw [hc1] at hc
      obtain ⟨K1, hK1⟩ := h1.1 a s1 hc1
      obtain ⟨K2, hK2⟩ := (h2 a s1 hc1).2 e s2 hc hf
      refine ⟨max K1 K2, fun k hk => ?_⟩
      show (g1 k >>= fun a => g2 a k) s = _
      rw [bind_apply, hK1 k (Nat.le_trans (Nat.le_max_left _ _) hk)]
      exact hK2 k (Nat.le_trans (Nat.le_max_right _ _) hk)

theorem EventualM.refl (c : M α) (s : St) : EventualM c (fun _ => c) s :=
  ⟨fun a s1 h => ⟨0, fun _ _ => h⟩, fun e s1 h _ => ⟨0, fun _ _ => h⟩⟩

theorem SimE.of_stops {cx : FnCtx} {pt : Pt} {fr : Frame} {c : M α} {c' : M β}
    {p : α → Pt → Frame → Prop} {q : β → Pt → Frame → Prop}
    (hn : ∀ s b s1, c' s ≠ .ok b s1) (hst : ∀ s e s1, c' s = .stop e s1 → c s = .stop e s1)
    (h : SimE cx pt fr c p) : SimE cx pt fr c' q := by
  intro s
  refine ⟨fun b s1 hc => absurd hc (hn s b s1), fun e s1 hc hf => ?_⟩
  exact (h s).2 e s1 (hst s e s1 hc) hf

/-- A computation that never finishes and only stops with faults or timeouts is matched by anything. -/
theorem SimE.vacuous {cx : FnCtx} {pt : Pt} {fr : Frame} {c : M α} {p : α → Pt → Frame → Prop}
    (h : ∀ s, (∀ a s1, c s ≠ .ok a s1) ∧ (∀ e s1, c s = .stop e s1 → ¬ IsFinal e)) :
    SimE cx pt fr c p := by
  intro s
  refine ⟨fun a s1 hc => absurd hc ((h s).1 a s1), fun e s1 hc hf => absurd hf ((h s).2 e s1 hc)⟩

theorem SimE.of_timeout {cx : FnCtx} {pt : Pt} {fr : Frame} {p : α → Pt → Frame → Prop} :
    SimE cx pt fr (Goose.Core.timeout : M α) p :=
  SimE.vacuous fun s => ⟨fun a s1 => by simp [Goose.Core.timeout, M.stop],
    fun e s1 hc => by
      simp [Goose.Core.timeout, M.stop] at hc
      obtain ⟨rfl, _⟩ := hc
      simp [IsFinal]⟩

/-- A computation that raises a fault is matched by anything. -/
theorem SimE.of_fault {cx : FnCtx} {pt : Pt} {fr : Frame} {k : FaultKind} {p : α → Pt → Frame → Prop} :
    SimE cx pt fr (Goose.Core.fault k : M α) p :=
  SimE.vacuous fun s => ⟨fun a s1 => by simp [Goose.Core.fault, M.stop],
    fun e s1 hc => by
      simp [Goose.Core.fault, M.stop] at hc
      obtain ⟨rfl, _⟩ := hc
      simp [IsFinal]⟩


theorem SimE.of_fault_bind {cx : FnCtx} {pt : Pt} {fr : Frame} {x : M β} {f : β → M α}
    {p : α → Pt → Frame → Prop}
    (hx : ∀ s, ∃ k s1, x s = .stop (.fault k) s1) : SimE cx pt fr (x >>= f) p := by
  refine SimE.vacuous fun s => ⟨fun a s1 hc => ?_, fun e s1 hc hf => ?_⟩
  · obtain ⟨k, s0, h⟩ := hx s
    rw [bind_apply, h] at hc
    cases hc
  · obtain ⟨k, s0, h⟩ := hx s
    rw [bind_apply, h] at hc
    cases hc
    simp [IsFinal] at hf

theorem SimE.expectInt {cx : FnCtx} {pt : Pt} {fr : Frame} {va : Val} {f : IntTy × Int → M α}
    {p : α → Pt → Frame → Prop} (h : ∀ t x, va = .int t x → SimE cx pt fr (f (t, x)) p) :
    SimE cx pt fr (Goose.Core.expectInt va >>= f) p := by
  cases va with
  | int t x => exact h t x rfl
  | _ => exact SimE.of_fault_bind fun s => ⟨_, s, rfl⟩

theorem SimE.expectBool {cx : FnCtx} {pt : Pt} {fr : Frame} {va : Val} {f : Bool → M α}
    {p : α → Pt → Frame → Prop} (h : ∀ b, va = .bool b → SimE cx pt fr (f b) p) :
    SimE cx pt fr (Goose.Core.expectBool va >>= f) p := by
  cases va with
  | bool b => exact h b rfl
  | _ => exact SimE.of_fault_bind fun s => ⟨_, s, rfl⟩

theorem SimE.expectRef {cx : FnCtx} {pt : Pt} {fr : Frame} {va : Val} {f : Loc → M α}
    {p : α → Pt → Frame → Prop} (h : ∀ l, va = .ref l → SimE cx pt fr (f l) p) :
    SimE cx pt fr (Goose.Core.expectRef va >>= f) p := by
  cases va with
  | ref l => exact h l rfl
  | _ => exact SimE.of_fault_bind fun s => ⟨_, s, rfl⟩

theorem SimE.expectRef' {cx : FnCtx} {pt : Pt} {fr : Frame} {va : Val} {p : Loc → Pt → Frame → Prop}
    (h : ∀ l, va = .ref l → SimE cx pt fr (Pure.pure l : M Loc) p) :
    SimE cx pt fr (Goose.Core.expectRef va) p := by
  have := SimE.expectRef (f := Pure.pure) (pt := pt) (fr := fr) (cx := cx) (p := p) h
  simpa using this

theorem SimE.expectSlice {cx : FnCtx} {pt : Pt} {fr : Frame} {va : Val}
    {f : Loc × Nat × Nat → M α} {p : α → Pt → Frame → Prop}
    (h : ∀ l st n, va = .slice l st n → SimE cx pt fr (f (l, st, n)) p) :
    SimE cx pt fr (Goose.Core.expectSlice va >>= f) p := by
  cases va with
  | slice l st n => exact h l st n rfl
  | _ => exact SimE.of_fault_bind fun s => ⟨_, s, rfl⟩

theorem SimE.expectSameTy {cx : FnCtx} {pt : Pt} {fr : Frame} {t u : IntTy} {f : Unit → M α}
    {p : α → Pt → Frame → Prop} (h : t = u → SimE cx pt fr (f ()) p) :
    SimE cx pt fr (Goose.Core.expectSameTy t u >>= f) p := by
  by_cases htu : t = u
  · subst htu
    simp only [Goose.Core.expectSameTy, ite_true]
    exact h rfl
  · exact SimE.of_fault_bind fun s => ⟨.shape, s, by simp [Goose.Core.expectSameTy, htu, Goose.Core.fault, M.stop]⟩

theorem SimE.expectIntTy {cx : FnCtx} {pt : Pt} {fr : Frame} {t : Ty} {f : IntTy → M α}
    {p : α → Pt → Frame → Prop} (h : ∀ d, t = .int d → SimE cx pt fr (f d) p) :
    SimE cx pt fr (Goose.Core.expectIntTy t >>= f) p := by
  cases t with
  | int d => exact h d rfl
  | _ => exact SimE.of_fault_bind fun s => ⟨_, s, rfl⟩

theorem SimE.expectFixedCount {cx : FnCtx} {pt : Pt} {fr : Frame} {t : Ty} {f : Nat → M α}
    {p : α → Pt → Frame → Prop} (h : ∀ e k, t = .arr e k → SimE cx pt fr (f k) p) :
    SimE cx pt fr (Goose.Core.expectFixedCount t >>= f) p := by
  cases t with
  | arr e k => exact h e k rfl
  | _ => exact SimE.of_fault_bind fun s => ⟨_, s, rfl⟩

theorem SimE.render {cx : FnCtx} {pt : Pt} {fr : Frame} {v : Val} {f : String → M α}
    {p : α → Pt → Frame → Prop}
    (h : ∀ str, Goose.Core.render v = pure str → SimE cx pt fr (f str) p) :
    SimE cx pt fr (Goose.Core.render v >>= f) p := by
  cases v with
  | int t n => exact h (toString n) rfl
  | bool b => cases b <;> exact h _ rfl
  | _ => exact SimE.of_fault_bind fun s => ⟨_, s, rfl⟩


theorem SimE.mono_goes {cx : FnCtx} {pt : Pt} {fr : Frame} {c : M α}
    {p q : α → Pt → Frame → Prop} (h : SimE cx pt fr c p)
    (hq : ∀ a pt' fr', p a pt' fr' → ∃ pt'' fr'', Goes cx pt' fr' pt'' fr'' ∧ q a pt'' fr'') :
    SimE cx pt fr c q := by
  intro s
  refine ⟨fun a s1 hc => ?_, (h s).2⟩
  obtain ⟨pt', fr', hp, he⟩ := (h s).1 a s1 hc
  obtain ⟨pt'', fr'', ⟨d, hd⟩, hq'⟩ := hq a pt' fr' hp
  refine ⟨pt'', fr'', hq', fun j result hf hr => ?_⟩
  exact he (j + d) result hf ((congrFun (hd j) s1).trans hr)

theorem SimE.def_step {cx : FnCtx} {pt : Pt} {fr : Frame} {r : ValueId} {op : Op}
    {c : M α} (inj : α → RVal) (hi : instAt cx.fn pt = some (.def r op))
    (hx : ∀ s, EventualM (c >>= fun a => pure (inj a)) (fun k => execOp k cx fr op) s) :
    SimE cx pt fr c (fun a pt' fr' => pt' = (pt.1, pt.2 + 1) ∧ fr' = fr.set r (inj a)) := by
  have key : ∀ k, runAt cx pt fr (k + 1) =
      (execOp k cx fr op >>= fun x => runAt cx (pt.1, pt.2 + 1) (fr.set r x) k) := by
    intro k
    unfold runAt
    rw [instsAt_cons hi, exec]
    simp only [setCell_eq, pure_bind]
  intro s
  refine ⟨?_, ?_⟩
  · intro a s1 hc
    have hc' : (c >>= fun a => pure (inj a)) s = .ok (inj a) s1 := by
      simp only [bind_apply, hc, pure_apply]
    obtain ⟨K, hK⟩ := (hx s).1 (inj a) s1 hc'
    refine ⟨(pt.1, pt.2 + 1), fr.set r (inj a), ⟨rfl, rfl⟩,
      fun j result hf hr => ⟨max K j + 1, fun k hk => ?_⟩⟩
    obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
    simp only [key l, bind_apply, hK l (by omega)]
    exact runAt_fuel_mono (by omega) cx _ _ s1 hf hr
  · intro e s1 hc hf
    have hc' : (c >>= fun a => pure (inj a)) s = .stop e s1 := by
      rw [bind_apply, hc]
    obtain ⟨K, hK⟩ := (hx s).2 e s1 hc' hf
    refine ⟨K + 1, fun k hk => ?_⟩
    obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
    simp only [key l, bind_apply, hK l (by omega)]

theorem SimE.eff_step {cx : FnCtx} {pt : Pt} {fr : Frame} {e : Effect} {c : M α}
    (fr' : α → Frame) (hi : instAt cx.fn pt = some (.eff e))
    (hx : execEff cx.fn fr e = c >>= fun a => pure (fr' a)) :
    SimE cx pt fr c (fun a pt' fr'' => pt' = (pt.1, pt.2 + 1) ∧ fr'' = fr' a) :=
  SimE.of_simG (SimG.eff_step fr' hi hx)

theorem SimE.abort_term {cx : FnCtx} {pt : Pt} {fr : Frame} {k : AbortKind} {org : OriginId}
    {p : α → Pt → Frame → Prop} (hi : instAt cx.fn pt = some (.term (.abort k (some org)))) :
    SimE cx pt fr (abortAt k org : M α) p := SimE.of_simG (SimG.abort_term hi)

theorem SimE.exit_term {cx : FnCtx} {pt : Pt} {fr : Frame} {v : ValueId} {org : Option OriginId}
    {t : IntTy} {n : Int} {p : α → Pt → Frame → Prop}
    (hi : instAt cx.fn pt = some (.term (.exit v org))) (hv : fr.vals[v]? = some (.val (.int t n))) :
    SimE cx pt fr (M.stop (.exit n) : M α) p := SimE.of_simG (SimG.exit_term hi hv)

theorem SimE.complete {cx : FnCtx} {pt : Pt} {fr : Frame} {c : M Val}
    {post : Val → Pt → Frame → Prop} (h : SimE cx pt fr c post)
    (ht : ∀ a pt' fr', post a pt' fr' → ∃ j, runAt cx pt' fr' j = pure a) (s : St) :
    EventualM c (fun k => runAt cx pt fr k) s := by
  refine ⟨fun a s1 hc => ?_, (h s).2⟩
  obtain ⟨pt', fr', hp, he⟩ := (h s).1 a s1 hc
  obtain ⟨j, hj⟩ := ht a pt' fr' hp
  exact he j (.ok a s1) (NonTimeout.ok a s1) (by rw [hj, pure_apply])

theorem EventualM.shift {c : M α} {g g' : Nat → M α} {s : St} (d : Nat)
    (h : EventualM c g s) (hg : ∀ k, g' (k + d) = g k) : EventualM c g' s := by
  refine ⟨?_, ?_⟩
  · intro a s1 hc
    obtain ⟨K, hK⟩ := h.1 a s1 hc
    refine ⟨K + d, fun k hk => ?_⟩
    obtain ⟨l, rfl⟩ : ∃ l, k = l + d := ⟨k - d, by omega⟩
    rw [hg]
    exact hK l (by omega)
  · intro e s1 hc hf
    obtain ⟨K, hK⟩ := h.2 e s1 hc hf
    refine ⟨K + d, fun k hk => ?_⟩
    obtain ⟨l, rfl⟩ : ∃ l, k = l + d := ⟨k - d, by omega⟩
    rw [hg]
    exact hK l (by omega)

theorem SimE.call_step {cx : FnCtx} {pt : Pt} {fr : Frame} {r : ValueId} {f : FnId}
    {args : List ValueId} {vals : List Val} {org : Option OriginId} {c : M Val}
    (hi : instAt cx.fn pt = some (.def r (.call f args org)))
    (ha : mapList (getVal fr) args = pure vals)
    (hc : ∀ s, EventualM c (fun k => callFn k cx.cfg fr.depth f vals) s) :
    SimE cx pt fr c (fun a pt' fr' => pt' = (pt.1, pt.2 + 1) ∧ fr' = fr.set r (.val a)) := by
  refine SimE.def_step RVal.val hi fun s => ?_
  have hmap := EventualM.bind (c2 := fun a => pure (RVal.val a))
    (g2 := fun a _ => pure (RVal.val a)) (hc s)
    (fun a s1 _ => EventualM.refl (pure (RVal.val a) : M RVal) s1)
  refine EventualM.shift 1 hmap fun k => ?_
  simp only [execOp, ha, pure_bind]

theorem SimE.complete_ret1 {cx : FnCtx} {pt : Pt} {fr : Frame} {c : M Val}
    {post : Val → Pt → Frame → Prop} {r : ValueId} {org : Option OriginId}
    (h : SimE cx pt fr c post)
    (ht : ∀ a pt' fr', post a pt' fr' →
      instAt cx.fn pt' = some (.term (.ret [r] org)) ∧ fr'.vals[r]? = some (.val a)) (s : St) :
    EventualM c (fun k => runAt cx pt fr k) s := by
  refine h.complete (fun a pt' fr' hp => ?_) s
  obtain ⟨hi, hv⟩ := ht a pt' fr' hp
  exact ⟨1, runAt_ret1 hi hv 0⟩

theorem SimE.complete_ret0 {cx : FnCtx} {pt : Pt} {fr : Frame} {c : M Val}
    {post : Val → Pt → Frame → Prop} {org : Option OriginId} (h : SimE cx pt fr c post)
    (ht : ∀ a pt' fr', post a pt' fr' →
      instAt cx.fn pt' = some (.term (.ret [] org)) ∧ a = .unit) (s : St) :
    EventualM c (fun k => runAt cx pt fr k) s := by
  refine h.complete (fun a pt' fr' hp => ?_) s
  obtain ⟨hi, rfl⟩ := ht a pt' fr' hp
  exact ⟨1, runAt_ret0 hi 0⟩

end Goose.Lower
