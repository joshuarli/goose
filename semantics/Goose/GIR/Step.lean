import Goose.GIR.Lemmas

/-!
Running a function from a program point, and the simulation judgment the proof
of the lowering is stated in.

A program point is a block and the number of instructions of that block that
have run. `runAt` runs the rest of the function from there. `SimG` says that a
Core computation is matched by running instructions from a program point: when
the computation finishes, running from the point with `k` more units of fuel
than some later program point needs is the same as running from that later
point, in the state the computation ended in; when it aborts or exits, running
stops the same way. The fuel is existential, and the equation holds for every
additional amount, so a fuel that is large enough for the whole run can be
chosen at the end.
-/

namespace Goose.GIR

open Goose.Core

/-- A stop that the lowering preserves: an abort or an exit. -/
def IsFinal : Stop → Prop
  | .abort .. => True
  | .exit _ => True
  | _ => False

/-- A block and the number of its instructions already run. -/
abbrev Pt := BlockId × Nat

/-- The instruction at a program point. -/
def instAt (fn : Func) (pt : Pt) : Option Inst :=
  (fn.blocks[pt.1]?).bind fun b => b.insts[pt.2]?

/-- The instructions from a program point to the end of its block. -/
def instsAt (fn : Func) (pt : Pt) : List Inst :=
  ((fn.blocks[pt.1]?).map fun b => b.insts.drop pt.2).getD []

/-- Run the rest of the function from a program point, with a given frame. -/
def runAt (cx : FnCtx) (pt : Pt) (fr : Frame) (j : Nat) : M Val :=
  exec j cx fr (instsAt cx.fn pt)

theorem instsAt_cons {fn : Func} {pt : Pt} {i : Inst} (h : instAt fn pt = some i) :
    instsAt fn pt = i :: instsAt fn (pt.1, pt.2 + 1) := by
  unfold instAt at h
  unfold instsAt
  cases hb : fn.blocks[pt.1]? with
  | none => simp [hb] at h
  | some blk =>
    simp only [hb, Option.bind_some] at h
    simp only [Option.map_some, Option.getD_some]
    rw [List.drop_eq_getElem_cons (by simpa using (List.getElem?_eq_some_iff.mp h).1)]
    simp only [List.cons.injEq, and_true]
    exact (List.getElem?_eq_some_iff.mp h).2

/-- A frame with one more cell. -/
def Frame.set (fr : Frame) (r : ValueId) (x : RVal) : Frame := { fr with vals := fr.vals.insert r x }

theorem setCell_eq (fr : Frame) (r : ValueId) (x : RVal) : setCell fr r x = pure (fr.set r x) := rfl

/-- Control moves from one program point to another, in any state, using no memory. -/
def Goes (cx : FnCtx) (pt : Pt) (fr : Frame) (pt' : Pt) (fr' : Frame) : Prop :=
  ∃ k, ∀ j, runAt cx pt fr (j + k) = runAt cx pt' fr' j

theorem Goes.refl (cx : FnCtx) (pt : Pt) (fr : Frame) : Goes cx pt fr pt fr := ⟨0, fun _ => rfl⟩

theorem Goes.trans {cx : FnCtx} {pt1 pt2 pt3 : Pt} {fr1 fr2 fr3 : Frame}
    (h1 : Goes cx pt1 fr1 pt2 fr2) (h2 : Goes cx pt2 fr2 pt3 fr3) : Goes cx pt1 fr1 pt3 fr3 := by
  obtain ⟨k1, h1⟩ := h1
  obtain ⟨k2, h2⟩ := h2
  refine ⟨k2 + k1, fun j => ?_⟩
  rw [show j + (k2 + k1) = (j + k2) + k1 by omega, h1, h2]

/-- `c` is matched by running from a program point (see the module comment). -/
def SimG (cx : FnCtx) (pt : Pt) (fr : Frame) (c : M α) (post : α → Pt → Frame → Prop) : Prop :=
  ∀ s, (∀ a s1, c s = .ok a s1 →
        ∃ pt' fr' k, post a pt' fr' ∧ ∀ j, runAt cx pt fr (j + k) s = runAt cx pt' fr' j s1) ∧
       (∀ e s1, c s = .stop e s1 → IsFinal e →
        ∃ k, ∀ j, runAt cx pt fr (j + k) s = .stop e s1)

theorem SimG.ret {cx : FnCtx} {pt : Pt} {fr : Frame} {a : α} {post : α → Pt → Frame → Prop}
    (h : post a pt fr) : SimG cx pt fr (Pure.pure a : M α) post := by
  intro s
  refine ⟨fun a' s1 hc => ?_, fun e s1 hc _ => ?_⟩
  · rw [pure_apply] at hc
    cases hc
    exact ⟨pt, fr, 0, h, fun _ => rfl⟩
  · rw [pure_apply] at hc
    cases hc

theorem SimG.mono {cx : FnCtx} {pt : Pt} {fr : Frame} {c : M α} {p q : α → Pt → Frame → Prop}
    (h : SimG cx pt fr c p) (hpq : ∀ a pt' fr', p a pt' fr' → q a pt' fr') : SimG cx pt fr c q := by
  intro s
  refine ⟨fun a s1 hc => ?_, (h s).2⟩
  obtain ⟨pt', fr', k, hp, he⟩ := (h s).1 a s1 hc
  exact ⟨pt', fr', k, hpq a pt' fr' hp, he⟩

theorem SimG.bind {cx : FnCtx} {pt : Pt} {fr : Frame} {c1 : M α} {p1 : α → Pt → Frame → Prop}
    {c2 : α → M β} {p2 : β → Pt → Frame → Prop}
    (h1 : SimG cx pt fr c1 p1)
    (h2 : ∀ a pt1 fr1, p1 a pt1 fr1 → SimG cx pt1 fr1 (c2 a) p2) :
    SimG cx pt fr (c1 >>= c2) p2 := by
  intro s
  refine ⟨fun b s2 hc => ?_, fun e s2 hc hf => ?_⟩
  · rw [bind_apply] at hc
    cases hc1 : c1 s with
    | stop e s1 => rw [hc1] at hc; cases hc
    | ok a s1 =>
      rw [hc1] at hc
      obtain ⟨pt1, fr1, k1, hp1, he1⟩ := (h1 s).1 a s1 hc1
      obtain ⟨pt2, fr2, k2, hp2, he2⟩ := ((h2 a pt1 fr1 hp1) s1).1 b s2 hc
      refine ⟨pt2, fr2, k2 + k1, hp2, fun j => ?_⟩
      rw [show j + (k2 + k1) = (j + k2) + k1 by omega, he1, he2]
  · rw [bind_apply] at hc
    cases hc1 : c1 s with
    | stop e1 s1 =>
      rw [hc1] at hc
      cases hc
      exact (h1 s).2 e s2 hc1 hf
    | ok a s1 =>
      rw [hc1] at hc
      obtain ⟨pt1, fr1, k1, hp1, he1⟩ := (h1 s).1 a s1 hc1
      obtain ⟨k2, he2⟩ := ((h2 a pt1 fr1 hp1) s1).2 e s2 hc hf
      refine ⟨k2 + k1, fun j => ?_⟩
      rw [show j + (k2 + k1) = (j + k2) + k1 by omega, he1, he2]

theorem SimG.goes {cx : FnCtx} {pt pt1 : Pt} {fr fr1 : Frame} {c : M α} {p : α → Pt → Frame → Prop}
    (hg : Goes cx pt fr pt1 fr1) (h : SimG cx pt1 fr1 c p) : SimG cx pt fr c p := by
  obtain ⟨k0, hk0⟩ := hg
  intro s
  refine ⟨fun a s1 hc => ?_, fun e s1 hc hf => ?_⟩
  · obtain ⟨pt', fr', k, hp, he⟩ := (h s).1 a s1 hc
    refine ⟨pt', fr', k + k0, hp, fun j => ?_⟩
    rw [show j + (k + k0) = (j + k) + k0 by omega, hk0, he]
  · obtain ⟨k, he⟩ := (h s).2 e s1 hc hf
    refine ⟨k + k0, fun j => ?_⟩
    rw [show j + (k + k0) = (j + k) + k0 by omega, hk0, he]

/-- A computation that never finishes is matched wherever another computation that stops the same
way is. -/
theorem SimG.of_stops {cx : FnCtx} {pt : Pt} {fr : Frame} {c : M α} {c' : M β}
    {p : α → Pt → Frame → Prop} {q : β → Pt → Frame → Prop}
    (hn : ∀ s b s1, c' s ≠ .ok b s1) (hst : ∀ s e s1, c' s = .stop e s1 → c s = .stop e s1)
    (h : SimG cx pt fr c p) : SimG cx pt fr c' q := by
  intro s
  refine ⟨fun b s1 hc => absurd hc (hn s b s1), fun e s1 hc hf => ?_⟩
  exact (h s).2 e s1 (hst s e s1 hc) hf

/-- A computation that never finishes and only stops with faults or timeouts is matched by anything. -/
theorem SimG.vacuous {cx : FnCtx} {pt : Pt} {fr : Frame} {c : M α} {p : α → Pt → Frame → Prop}
    (h : ∀ s, (∀ a s1, c s ≠ .ok a s1) ∧ (∀ e s1, c s = .stop e s1 → ¬ IsFinal e)) :
    SimG cx pt fr c p := by
  intro s
  refine ⟨fun a s1 hc => absurd hc ((h s).1 a s1), fun e s1 hc hf => absurd hf ((h s).2 e s1 hc)⟩

theorem SimG.of_timeout {cx : FnCtx} {pt : Pt} {fr : Frame} {p : α → Pt → Frame → Prop} :
    SimG cx pt fr (Goose.Core.timeout : M α) p :=
  SimG.vacuous fun s => ⟨fun a s1 => by simp [Goose.Core.timeout, M.stop],
    fun e s1 hc => by
      simp [Goose.Core.timeout, M.stop] at hc
      obtain ⟨rfl, _⟩ := hc
      simp [IsFinal]⟩

/-- A computation that raises a fault is matched by anything. -/
theorem SimG.of_fault {cx : FnCtx} {pt : Pt} {fr : Frame} {k : FaultKind} {p : α → Pt → Frame → Prop} :
    SimG cx pt fr (Goose.Core.fault k : M α) p :=
  SimG.vacuous fun s => ⟨fun a s1 => by simp [Goose.Core.fault, M.stop],
    fun e s1 hc => by
      simp [Goose.Core.fault, M.stop] at hc
      obtain ⟨rfl, _⟩ := hc
      simp [IsFinal]⟩

/-! ### One instruction -/

/-- A defining instruction whose operation computes what `c` does. -/
theorem SimG.def_step {cx : FnCtx} {pt : Pt} {fr : Frame} {r : ValueId} {op : Op} {c : M α}
    (inj : α → RVal) (hi : instAt cx.fn pt = some (.def r op)) (hnc : ∀ f a o, op ≠ .call f a o)
    (hx : execPure cx fr op = c >>= fun a => pure (inj a)) :
    SimG cx pt fr c (fun a pt' fr' => pt' = (pt.1, pt.2 + 1) ∧ fr' = fr.set r (inj a)) := by
  have hop : ∀ n, execOp n cx fr op = execPure cx fr op := by
    intro n
    cases op with
    | call f a o => exact absurd rfl (hnc f a o)
    | _ => unfold execOp; rfl
  have key : ∀ j s, runAt cx pt fr (j + 1) s =
      (match c s with
       | .ok a s1 => runAt cx (pt.1, pt.2 + 1) (fr.set r (inj a)) j s1
       | .stop e s1 => .stop e s1) := by
    intro j s
    unfold runAt
    rw [instsAt_cons hi, show j + 1 = j + 1 from rfl, exec, bind_apply, hop, hx]
    simp only [bind_apply, bind_assoc, pure_bind]
    cases c s with
    | stop e s1 => rfl
    | ok a s1 => rfl
  intro s
  refine ⟨fun a s1 hc => ?_, fun e s1 hc _ => ?_⟩
  · refine ⟨_, _, 1, ⟨rfl, rfl⟩, fun j => ?_⟩
    rw [key j s, hc]
  · refine ⟨1, fun j => ?_⟩
    rw [key j s, hc]

/-- An effect that computes what `c` does and leaves the frame `fr'`. -/
theorem SimG.eff_step {cx : FnCtx} {pt : Pt} {fr : Frame} {e : Effect} {c : M α} (fr' : α → Frame)
    (hi : instAt cx.fn pt = some (.eff e))
    (hx : execEff cx.fn fr e = c >>= fun a => pure (fr' a)) :
    SimG cx pt fr c (fun a pt' fr'' => pt' = (pt.1, pt.2 + 1) ∧ fr'' = fr' a) := by
  have key : ∀ j s, runAt cx pt fr (j + 1) s =
      (match c s with
       | .ok a s1 => runAt cx (pt.1, pt.2 + 1) (fr' a) j s1
       | .stop e s1 => .stop e s1) := by
    intro j s
    unfold runAt
    rw [instsAt_cons hi, exec, bind_apply, hx]
    simp only [bind_apply, bind_assoc, pure_bind]
    cases c s with
    | stop e s1 => rfl
    | ok a s1 => rfl
  intro s
  refine ⟨fun a s1 hc => ?_, fun e s1 hc _ => ?_⟩
  · refine ⟨_, _, 1, ⟨rfl, rfl⟩, fun j => ?_⟩
    rw [key j s, hc]
  · refine ⟨1, fun j => ?_⟩
    rw [key j s, hc]

/-! ### Control transfer -/

theorem cells_args {fr : Frame} : ∀ {args : List ValueId} {xs : List RVal},
    (∀ a ∈ args, ∃ x, fr.vals[a]? = some x) → ∃ ys, mapList (getCell fr) args = pure ys
  | [], _, _ => ⟨[], rfl⟩
  | a :: as, _, h => by
    obtain ⟨x, hx⟩ := h a (by simp)
    obtain ⟨ys, hys⟩ := cells_args (fr := fr) (args := as) (xs := []) (fun b hb => h b (by simp [hb]))
    exact ⟨x :: ys, by simp only [mapList, getCell_of hx, pure_bind, hys]⟩

theorem goes_br0 {cx : FnCtx} {pt : Pt} {fr : Frame} {b : BlockId} {blk : Block}
    (hi : instAt cx.fn pt = some (.term (.br b [])))
    (hb : cx.fn.blocks[b]? = some blk) (hp : blk.params = []) :
    Goes cx pt fr (b, 0) fr := by
  refine ⟨1, fun j => ?_⟩
  unfold runAt
  rw [instsAt_cons hi, exec]
  simp only [mapList, pure_bind, enterBlock, hb, hp, List.length_nil, ↓reduceIte, bindParams]
  have : instsAt cx.fn (b, 0) = blk.insts := by simp [instsAt, hb]
  rw [this]

theorem goes_br1 {cx : FnCtx} {pt : Pt} {fr : Frame} {b : BlockId} {blk : Block} {v p : ValueId}
    {ty : VTy} {x : RVal}
    (hi : instAt cx.fn pt = some (.term (.br b [v])))
    (hb : cx.fn.blocks[b]? = some blk) (hp : blk.params = [(p, ty)]) (hx : fr.vals[v]? = some x) :
    Goes cx pt fr (b, 0) (fr.set p x) := by
  refine ⟨1, fun j => ?_⟩
  unfold runAt
  rw [instsAt_cons hi, exec]
  simp only [mapList, getCell_of hx, pure_bind, enterBlock, hb, hp, List.length_cons, List.length_nil,
    ↓reduceIte, bindParams, setCell_eq]
  have : instsAt cx.fn (b, 0) = blk.insts := by simp [instsAt, hb]
  rw [this]

theorem goes_condbr {cx : FnCtx} {pt : Pt} {fr : Frame} {c : ValueId} {tb eb : BlockId}
    {tblk eblk : Block} {β : Bool}
    (hi : instAt cx.fn pt = some (.term (.condbr c tb [] eb [])))
    (hc : fr.vals[c]? = some (.val (.bool β)))
    (ht : cx.fn.blocks[tb]? = some tblk) (htp : tblk.params = [])
    (he : cx.fn.blocks[eb]? = some eblk) (hep : eblk.params = []) :
    Goes cx pt fr (if β then (tb, 0) else (eb, 0)) fr := by
  refine ⟨1, fun j => ?_⟩
  unfold runAt
  rw [instsAt_cons hi, exec]
  cases β
  · simp only [getVal_of hc, Goose.Core.expectBool, pure_bind, Bool.false_eq_true, ↓reduceIte, mapList,
      enterBlock, he, hep, List.length_nil, bindParams]
    have : instsAt cx.fn (eb, 0) = eblk.insts := by simp [instsAt, he]
    rw [this]
  · simp only [getVal_of hc, Goose.Core.expectBool, pure_bind, ↓reduceIte, mapList,
      enterBlock, ht, htp, List.length_nil, bindParams]
    have : instsAt cx.fn (tb, 0) = tblk.insts := by simp [instsAt, ht]
    rw [this]

/-! ### Core's value tests -/

/-- A computation that always stops with a fault is matched by anything. -/
theorem SimG.of_fault_bind {cx : FnCtx} {pt : Pt} {fr : Frame} {x : M β} {f : β → M α}
    {p : α → Pt → Frame → Prop}
    (hx : ∀ s, ∃ k s1, x s = .stop (.fault k) s1) : SimG cx pt fr (x >>= f) p := by
  refine SimG.vacuous fun s => ⟨fun a s1 hc => ?_, fun e s1 hc hf => ?_⟩
  · obtain ⟨k, s0, h⟩ := hx s
    rw [bind_apply, h] at hc
    cases hc
  · obtain ⟨k, s0, h⟩ := hx s
    rw [bind_apply, h] at hc
    cases hc
    simp [IsFinal] at hf

theorem SimG.expectInt {cx : FnCtx} {pt : Pt} {fr : Frame} {va : Val} {f : IntTy × Int → M α}
    {p : α → Pt → Frame → Prop} (h : ∀ t x, va = .int t x → SimG cx pt fr (f (t, x)) p) :
    SimG cx pt fr (Goose.Core.expectInt va >>= f) p := by
  cases va with
  | int t x => exact h t x rfl
  | _ => exact SimG.of_fault_bind fun s => ⟨_, s, rfl⟩

theorem SimG.expectBool {cx : FnCtx} {pt : Pt} {fr : Frame} {va : Val} {f : Bool → M α}
    {p : α → Pt → Frame → Prop} (h : ∀ b, va = .bool b → SimG cx pt fr (f b) p) :
    SimG cx pt fr (Goose.Core.expectBool va >>= f) p := by
  cases va with
  | bool b => exact h b rfl
  | _ => exact SimG.of_fault_bind fun s => ⟨_, s, rfl⟩

theorem SimG.expectRef {cx : FnCtx} {pt : Pt} {fr : Frame} {va : Val} {f : Loc → M α}
    {p : α → Pt → Frame → Prop} (h : ∀ l, va = .ref l → SimG cx pt fr (f l) p) :
    SimG cx pt fr (Goose.Core.expectRef va >>= f) p := by
  cases va with
  | ref l => exact h l rfl
  | _ => exact SimG.of_fault_bind fun s => ⟨_, s, rfl⟩

theorem SimG.expectRef' {cx : FnCtx} {pt : Pt} {fr : Frame} {va : Val} {p : Loc → Pt → Frame → Prop}
    (h : ∀ l, va = .ref l → SimG cx pt fr (Pure.pure l : M Loc) p) :
    SimG cx pt fr (Goose.Core.expectRef va) p := by
  have := SimG.expectRef (f := Pure.pure) (pt := pt) (fr := fr) (cx := cx) (p := p) h
  simpa using this

theorem SimG.expectSlice {cx : FnCtx} {pt : Pt} {fr : Frame} {va : Val}
    {f : Loc × Nat × Nat → M α} {p : α → Pt → Frame → Prop}
    (h : ∀ l st n, va = .slice l st n → SimG cx pt fr (f (l, st, n)) p) :
    SimG cx pt fr (Goose.Core.expectSlice va >>= f) p := by
  cases va with
  | slice l st n => exact h l st n rfl
  | _ => exact SimG.of_fault_bind fun s => ⟨_, s, rfl⟩

theorem SimG.expectSameTy {cx : FnCtx} {pt : Pt} {fr : Frame} {t u : IntTy} {f : Unit → M α}
    {p : α → Pt → Frame → Prop} (h : t = u → SimG cx pt fr (f ()) p) :
    SimG cx pt fr (Goose.Core.expectSameTy t u >>= f) p := by
  by_cases htu : t = u
  · subst htu
    simp only [Goose.Core.expectSameTy, if_true]
    exact h rfl
  · exact SimG.of_fault_bind fun s => ⟨.shape, s, by simp [Goose.Core.expectSameTy, htu, Goose.Core.fault, M.stop]⟩

theorem SimG.expectIntTy {cx : FnCtx} {pt : Pt} {fr : Frame} {t : Ty} {f : IntTy → M α}
    {p : α → Pt → Frame → Prop} (h : ∀ d, t = .int d → SimG cx pt fr (f d) p) :
    SimG cx pt fr (Goose.Core.expectIntTy t >>= f) p := by
  cases t with
  | int d => exact h d rfl
  | _ => exact SimG.of_fault_bind fun s => ⟨_, s, rfl⟩

theorem SimG.expectFixedCount {cx : FnCtx} {pt : Pt} {fr : Frame} {t : Ty} {f : Nat → M α}
    {p : α → Pt → Frame → Prop} (h : ∀ e k, t = .arr e k → SimG cx pt fr (f k) p) :
    SimG cx pt fr (Goose.Core.expectFixedCount t >>= f) p := by
  cases t with
  | arr e k => exact h e k rfl
  | _ => exact SimG.of_fault_bind fun s => ⟨_, s, rfl⟩

theorem SimG.render {cx : FnCtx} {pt : Pt} {fr : Frame} {v : Val} {f : String → M α}
    {p : α → Pt → Frame → Prop}
    (h : ∀ str, Goose.Core.render v = pure str → SimG cx pt fr (f str) p) :
    SimG cx pt fr (Goose.Core.render v >>= f) p := by
  cases v with
  | int t n => exact h (toString n) rfl
  | bool b => cases b <;> exact h _ rfl
  | _ => exact SimG.of_fault_bind fun s => ⟨_, s, rfl⟩

/-! ### Pure operations on cells -/

theorem execPure_bin {cx : FnCtx} {fr : Frame} {cfg : Cfg} {op : BinOp} {t0 : IntTy} {xi yi : ValueId}
    {o : OriginId} {t : IntTy} {x y : Int}
    (hp : cx.cfg.profile = cfg.profile)
    (hx : fr.vals[xi]? = some (.val (.int t x))) (hy : fr.vals[yi]? = some (.val (.int t y))) :
    execPure cx fr (.bin op t0 xi yi (some o)) =
      (match evalBin cfg.profile op t x y with
       | .ok r => pure (Val.int t r)
       | .error k => abortAt (AbortKind.ofNum k) o) >>=
      fun a => pure (RVal.val a) := by
  simp only [execPure, getVal_of hx, getVal_of hy, bind_assoc, pure_bind, hp,
    Goose.Core.expectSameTy, Goose.Core.expectInt, ↓reduceIte]
  cases evalBin cfg.profile op t x y <;> rfl

theorem execPure_un {cx : FnCtx} {fr : Frame} {cfg : Cfg} {op : UnOp} {t0 : IntTy} {xi : ValueId}
    {o : OriginId} {t : IntTy} {x : Int}
    (hp : cx.cfg.profile = cfg.profile) (hx : fr.vals[xi]? = some (.val (.int t x))) :
    execPure cx fr (.un op t0 xi (some o)) =
      (match evalUn cfg.profile op t x with
       | .ok r => pure (Val.int t r)
       | .error k => abortAt (AbortKind.ofNum k) o) >>=
      fun a => pure (RVal.val a) := by
  simp only [execPure, getVal_of hx, bind_assoc, pure_bind, hp, Goose.Core.expectInt]
  cases evalUn cfg.profile op t x <;> rfl

theorem execPure_cmp {cx : FnCtx} {fr : Frame} {op : CmpOp} {xi yi : ValueId}
    {va vb : Val} (hx : fr.vals[xi]? = some (.val va)) (hy : fr.vals[yi]? = some (.val vb)) :
    (∀ t0, execPure cx fr (.cmp op t0 xi yi) =
      (expectComparable va vb >>= fun p => pure (Val.bool (evalCmp op p.1 p.2))) >>=
        fun a => pure (RVal.val a)) ∧
    (execPure cx fr (.boolCmp op xi yi) =
      (expectComparable va vb >>= fun p => pure (Val.bool (evalCmp op p.1 p.2))) >>=
        fun a => pure (RVal.val a)) := by
  refine ⟨fun t0 => ?_, ?_⟩ <;>
  simp only [execPure, getVal_of hx, getVal_of hy, bind_assoc, pure_bind]

theorem execPure_conv {cx : FnCtx} {fr : Frame} {cfg : Cfg} {k : ConvKind} {s0 : IntTy} {dst : IntTy}
    {xi : ValueId} {o : OriginId} {src : IntTy} {x : Int}
    (hp : cx.cfg.profile = cfg.profile) (hx : fr.vals[xi]? = some (.val (.int src x))) :
    execPure cx fr (.conv k s0 dst xi (some o)) =
      (match evalConv cfg.profile k src dst x with
       | .ok r => pure (Val.int dst r)
       | .error e => abortAt (AbortKind.ofNum e) o) >>=
      fun a => pure (RVal.val a) := by
  simp only [execPure, getVal_of hx, bind_assoc, pure_bind, hp, Goose.Core.expectInt]
  cases evalConv cfg.profile k src dst x <;> rfl

/-- A conditional branch taken to a block without parameters. -/
theorem goes_condbr_then0 {cx : FnCtx} {pt : Pt} {fr : Frame} {c : ValueId} {tb eb : BlockId}
    {targs eargs : List ValueId} {tblk : Block}
    (hi : instAt cx.fn pt = some (.term (.condbr c tb targs eb eargs)))
    (hc : fr.vals[c]? = some (.val (.bool true)))
    (ht : cx.fn.blocks[tb]? = some tblk) (htp : tblk.params = []) (hta : targs = []) :
    Goes cx pt fr (tb, 0) fr := by
  subst hta
  refine ⟨1, fun j => ?_⟩
  unfold runAt
  rw [instsAt_cons hi, exec]
  simp only [getVal_of hc, Goose.Core.expectBool, pure_bind, ↓reduceIte, mapList,
    enterBlock, ht, htp, List.length_nil, bindParams]
  have : instsAt cx.fn (tb, 0) = tblk.insts := by simp [instsAt, ht]
  rw [this]

theorem goes_condbr_else0 {cx : FnCtx} {pt : Pt} {fr : Frame} {c : ValueId} {tb eb : BlockId}
    {targs eargs : List ValueId} {eblk : Block}
    (hi : instAt cx.fn pt = some (.term (.condbr c tb targs eb eargs)))
    (hc : fr.vals[c]? = some (.val (.bool false)))
    (he : cx.fn.blocks[eb]? = some eblk) (hep : eblk.params = []) (hea : eargs = []) :
    Goes cx pt fr (eb, 0) fr := by
  subst hea
  refine ⟨1, fun j => ?_⟩
  unfold runAt
  rw [instsAt_cons hi, exec]
  simp only [getVal_of hc, Goose.Core.expectBool, pure_bind, Bool.false_eq_true, ↓reduceIte, mapList,
    enterBlock, he, hep, List.length_nil, bindParams]
  have : instsAt cx.fn (eb, 0) = eblk.insts := by simp [instsAt, he]
  rw [this]

/-- A conditional branch taken to a block with one parameter, passed a value. -/
theorem goes_condbr_then1 {cx : FnCtx} {pt : Pt} {fr : Frame} {c v p : ValueId} {tb eb : BlockId}
    {targs eargs : List ValueId} {tblk : Block} {ty : VTy} {x : RVal}
    (hi : instAt cx.fn pt = some (.term (.condbr c tb targs eb eargs)))
    (hc : fr.vals[c]? = some (.val (.bool true)))
    (ht : cx.fn.blocks[tb]? = some tblk) (htp : tblk.params = [(p, ty)]) (hta : targs = [v])
    (hx : fr.vals[v]? = some x) : Goes cx pt fr (tb, 0) (fr.set p x) := by
  subst hta
  refine ⟨1, fun j => ?_⟩
  unfold runAt
  rw [instsAt_cons hi, exec]
  simp only [getVal_of hc, Goose.Core.expectBool, pure_bind, ↓reduceIte, mapList, getCell_of hx,
    enterBlock, ht, htp, List.length_cons, List.length_nil, bindParams, setCell_eq]
  have : instsAt cx.fn (tb, 0) = tblk.insts := by simp [instsAt, ht]
  rw [this]

theorem goes_condbr_else1 {cx : FnCtx} {pt : Pt} {fr : Frame} {c v p : ValueId} {tb eb : BlockId}
    {targs eargs : List ValueId} {eblk : Block} {ty : VTy} {x : RVal}
    (hi : instAt cx.fn pt = some (.term (.condbr c tb targs eb eargs)))
    (hc : fr.vals[c]? = some (.val (.bool false)))
    (he : cx.fn.blocks[eb]? = some eblk) (hep : eblk.params = [(p, ty)]) (hea : eargs = [v])
    (hx : fr.vals[v]? = some x) : Goes cx pt fr (eb, 0) (fr.set p x) := by
  subst hea
  refine ⟨1, fun j => ?_⟩
  unfold runAt
  rw [instsAt_cons hi, exec]
  simp only [getVal_of hc, Goose.Core.expectBool, pure_bind, Bool.false_eq_true, ↓reduceIte, mapList,
    getCell_of hx, enterBlock, he, hep, List.length_cons, List.length_nil, bindParams, setCell_eq]
  have : instsAt cx.fn (eb, 0) = eblk.insts := by simp [instsAt, he]
  rw [this]

/-! ### Terminators that stop the run -/

theorem SimG.abort_term {cx : FnCtx} {pt : Pt} {fr : Frame} {k : AbortKind} {org : OriginId}
    {p : α → Pt → Frame → Prop} (hi : instAt cx.fn pt = some (.term (.abort k (some org)))) :
    SimG cx pt fr (abortAt k org : M α) p := by
  intro s
  refine ⟨fun a s1 hc => ?_, fun e s1 hc _ => ?_⟩
  · simp [abortAt, M.stop] at hc
  · simp only [abortAt, M.stop] at hc
    cases hc
    refine ⟨1, fun j => ?_⟩
    unfold runAt
    rw [instsAt_cons hi]
    simp [exec, abortAtOrg, abortAt, M.stop]

theorem SimG.exit_term {cx : FnCtx} {pt : Pt} {fr : Frame} {v : ValueId} {org : Option OriginId}
    {t : IntTy} {n : Int} {p : α → Pt → Frame → Prop}
    (hi : instAt cx.fn pt = some (.term (.exit v org))) (hv : fr.vals[v]? = some (.val (.int t n))) :
    SimG cx pt fr (M.stop (.exit n) : M α) p := by
  intro s
  refine ⟨fun a s1 hc => ?_, fun e s1 hc _ => ?_⟩
  · simp [M.stop] at hc
  · simp only [M.stop] at hc
    cases hc
    refine ⟨1, fun j => ?_⟩
    unfold runAt
    rw [instsAt_cons hi]
    simp [exec, getVal_of hv, Goose.Core.expectInt, M.stop]

theorem SimG.of_timeout_bind {cx : FnCtx} {pt : Pt} {fr : Frame} {f : α → M β}
    {p : β → Pt → Frame → Prop} : SimG cx pt fr ((Goose.Core.timeout : M α) >>= f) p := by
  refine SimG.vacuous fun s => ⟨fun a s1 hc => ?_, fun e s1 hc hf => ?_⟩
  · simp [bind_apply, Goose.Core.timeout, M.stop] at hc
  · simp [bind_apply, Goose.Core.timeout, M.stop] at hc
    obtain ⟨rfl, _⟩ := hc
    simp [IsFinal] at hf

/-- A match followed by a transfer of control. -/
theorem SimG.mono_goes {cx : FnCtx} {pt : Pt} {fr : Frame} {c : M α} {p q : α → Pt → Frame → Prop}
    (h : SimG cx pt fr c p)
    (hq : ∀ a pt' fr', p a pt' fr' → ∃ pt'' fr'', Goes cx pt' fr' pt'' fr'' ∧ q a pt'' fr'') :
    SimG cx pt fr c q := by
  intro s
  refine ⟨fun a s1 hc => ?_, (h s).2⟩
  obtain ⟨pt', fr', k, hp, he⟩ := (h s).1 a s1 hc
  obtain ⟨pt'', fr'', ⟨k2, hk2⟩, hq'⟩ := hq a pt' fr' hp
  refine ⟨pt'', fr'', k2 + k, hq', fun j => ?_⟩
  rw [show j + (k2 + k) = (j + k2) + k by omega, he, hk2]

theorem runAt_ret1 {cx : FnCtx} {pt : Pt} {fr : Frame} {r : ValueId} {org : Option OriginId} {v : Val}
    (hi : instAt cx.fn pt = some (.term (.ret [r] org))) (hv : fr.vals[r]? = some (.val v)) (j : Nat) :
    runAt cx pt fr (j + 1) = pure v := by
  unfold runAt
  rw [instsAt_cons hi]
  simp [exec, getVal_of hv]

theorem runAt_ret0 {cx : FnCtx} {pt : Pt} {fr : Frame} {org : Option OriginId}
    (hi : instAt cx.fn pt = some (.term (.ret [] org))) (j : Nat) :
    runAt cx pt fr (j + 1) = pure .unit := by
  unfold runAt
  rw [instsAt_cons hi]
  simp [exec]

end Goose.GIR
