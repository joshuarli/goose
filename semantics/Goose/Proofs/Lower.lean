import Goose.GIR.Eval
import Goose.Lower.CoreToGir

/-!
Forward simulation of Core's evaluator by the interpreter of the lowered
module.

Both interpreters run in the same monad `M` over the same state `St`, so the
state correspondence of the lowering is equality of states; what differs is the
environment: Core's `Env` against the interpreter's `Frame`.
-/

namespace Goose.Proofs.Lower

open Goose.Core Goose.GIR Goose.Lower

instance instLawfulMonadM : LawfulMonad M := LawfulMonad.mk'
  M
  (id_map := fun x => by
    funext s
    show (match x s with | .ok a s' => Res.ok a s' | .stop e s' => .stop e s') = x s
    cases x s <;> rfl)
  (pure_bind := fun a f => rfl)
  (bind_assoc := fun x f g => by
    funext s
    show (match (match x s with | .ok a s' => f a s' | .stop e s' => .stop e s') with
      | .ok a s' => g a s' | .stop e s' => .stop e s') =
      (match x s with
        | .ok a s' => (match f a s' with | .ok b s'' => g b s'' | .stop e s'' => .stop e s'')
        | .stop e s' => .stop e s')
    cases x s <;> rfl)

theorem bind_apply (x : M α) (f : α → M β) (s : St) :
    (x >>= f) s = (match x s with | .ok a s' => f a s' | .stop e s' => .stop e s') := rfl

theorem pure_apply (a : α) (s : St) : (pure a : M α) s = .ok a s := rfl

/-- A stop that the lowering preserves: an abort or an exit. -/
def IsFinal : Stop → Prop
  | .abort .. => True
  | .exit _ => True
  | _ => False

/-- The Core computation `c` is simulated by the interpreter computation `g`
that yields the next frame: whenever `c` finishes, `g` finishes in the same
state with a frame related to the result by `post`, and whenever `c` aborts or
exits, so does `g`, in the same state. -/
def Sim (c : M α) (g : M Frame) (post : α → Frame → Prop) : Prop :=
  ∀ s, (∀ a s1, c s = .ok a s1 → ∃ fr', g s = .ok fr' s1 ∧ post a fr') ∧
       (∀ e s1, c s = .stop e s1 → IsFinal e → g s = .stop e s1)

theorem Sim.pure' {a : α} {g : M Frame} {fr' : Frame} {post : α → Frame → Prop}
    (hg : g = pure fr') (h : post a fr') : Sim (pure a) g post := by
  intro s
  subst hg
  refine ⟨fun a' s1 hc => ?_, fun e s1 hc _ => ?_⟩
  · rw [pure_apply] at hc
    cases hc
    exact ⟨fr', rfl, h⟩
  · rw [pure_apply] at hc
    cases hc

theorem Sim.bind {c1 : M α} {g1 : M Frame} {p1 : α → Frame → Prop}
    {c2 : α → M β} {g2 : Frame → M Frame} {p2 : β → Frame → Prop}
    (h1 : Sim c1 g1 p1) (h2 : ∀ a fr, p1 a fr → Sim (c2 a) (g2 fr) p2) :
    Sim (c1 >>= c2) (g1 >>= g2) p2 := by
  intro s
  refine ⟨fun b s2 hc => ?_, fun e s2 hc hf => ?_⟩
  · rw [bind_apply] at hc
    cases hc1 : c1 s with
    | stop e s1 => rw [hc1] at hc; cases hc
    | ok a s1 =>
      rw [hc1] at hc
      obtain ⟨fr1, hg1, hp1⟩ := (h1 s).1 a s1 hc1
      obtain ⟨fr2, hg2, hp2⟩ := ((h2 a fr1 hp1) s1).1 b s2 hc
      refine ⟨fr2, ?_, hp2⟩
      rw [bind_apply, hg1]
      exact hg2
  · rw [bind_apply] at hc
    cases hc1 : c1 s with
    | stop e1 s1 =>
      rw [hc1] at hc
      cases hc
      rw [bind_apply, (h1 s).2 e s2 hc1 hf]
    | ok a s1 =>
      rw [hc1] at hc
      obtain ⟨fr1, hg1, hp1⟩ := (h1 s).1 a s1 hc1
      rw [bind_apply, hg1]
      exact ((h2 a fr1 hp1) s1).2 e s2 hc hf

theorem Sim.mono {c : M α} {g : M Frame} {p q : α → Frame → Prop}
    (h : Sim c g p) (hpq : ∀ a fr, p a fr → q a fr) : Sim c g q := by
  intro s
  refine ⟨fun a s1 hc => ?_, (h s).2⟩
  obtain ⟨fr', hg, hp⟩ := (h s).1 a s1 hc
  exact ⟨fr', hg, hpq a fr' hp⟩

/-! ### Straight-line code -/

/-- Run instructions that define values without calling, and effects, and
yield the frame. -/
def runS (cx : FnCtx) : Frame → List Inst → M Frame
  | fr, [] => pure fr
  | fr, .def r op :: rest => do
    let x ← execPure cx fr op
    let fr' ← setCell fr r x
    runS cx fr' rest
  | fr, .eff e :: rest => do
    let fr' ← execEff cx.fn fr e
    runS cx fr' rest
  | _, .term _ :: _ => fault .flow

def Straight1 : Inst → Prop
  | .def _ (.call ..) => False
  | .def _ _ => True
  | .eff _ => True
  | .term _ => False

def Straight (E : List Inst) : Prop := ∀ i ∈ E, Straight1 i

theorem execOp_pure (n : Nat) (cx : FnCtx) (fr : Frame) (op : Op)
    (h : ∀ f a o, op ≠ .call f a o) : execOp n cx fr op = execPure cx fr op := by
  cases op with
  | call f a o => exact absurd rfl (h f a o)
  | _ => unfold execOp; rfl

/-- Straight-line code costs one unit of fuel per instruction. -/
theorem exec_runS (cx : FnCtx) : ∀ (E : List Inst) (fr : Frame) (rest : List Inst) (j : Nat),
    Straight E → exec (j + E.length) cx fr (E ++ rest) =
      (runS cx fr E >>= fun fr' => exec j cx fr' rest)
  | [], fr, rest, j, _ => by
    simp [runS]
  | .def r op :: E, fr, rest, j, h => by
    have hop : ∀ f a o, op ≠ .call f a o := by
      intro f a o ho
      have := h (.def r op) (by simp)
      subst ho
      exact this
    have h' : Straight E := fun i hi => h i (by simp [hi])
    have : j + (E.length + 1) = (j + E.length) + 1 := by omega
    simp only [List.length_cons, this, List.cons_append]
    funext s
    rw [exec]
    simp only [runS, bind_apply]
    rw [execOp_pure _ _ _ _ hop]
    cases execPure cx fr op s with
    | stop e s1 => rfl
    | ok x s1 =>
      simp only [setCell, pure_apply]
      exact congrFun (exec_runS cx E _ rest j h') s1
  | .eff e :: E, fr, rest, j, h => by
    have h' : Straight E := fun i hi => h i (by simp [hi])
    have : j + (E.length + 1) = (j + E.length) + 1 := by omega
    simp only [List.length_cons, this, List.cons_append]
    funext s
    rw [exec]
    simp only [runS, bind_apply]
    cases execEff cx.fn fr e s with
    | stop e s1 => rfl
    | ok fr1 s1 =>
      exact congrFun (exec_runS cx E fr1 rest j h') s1
  | .term t :: E, fr, rest, j, h => absurd (h (.term t) (by simp)) (by simp [Straight1])

/-! ### What the builder emits -/

def defIds (E : List Inst) : List ValueId :=
  E.filterMap fun
    | .def r _ => some r
    | _ => none

/-- Effects that leave the entered scopes alone. -/
def EffPlain : Effect → Prop
  | .slotInit .. | .store .. | .append .. | .print .. => True
  | .enter _ | .leave _ => False

def plainInst : Inst → Prop
  | .def .. => True
  | .eff e => EffPlain e
  | .term _ => False

/-- Instructions that define values or write memory, and no more. -/
def NoScope (E : List Inst) : Prop := ∀ i ∈ E, plainInst i

/-- The builder, started with block `b` current, appended `E` to `b`, left `b`
current, created no block and touched no other block. -/
structure Em (b : BlockId) (ls ls' : LS) (E : List Inst) : Prop where
  cur : ls.cur = some b
  cur' : ls'.cur = some b
  blocks : ∀ i, ls'.blocks[i]? =
    if i = b then ls.blocks[i]?.map (fun blk => { blk with insts := blk.insts ++ E.toArray })
    else ls.blocks[i]?
  mono : ls.vals.size ≤ ls'.vals.size
  fresh : ∀ r ∈ defIds E, ls.vals.size ≤ r ∧ r < ls'.vals.size

theorem Em.refl {b : BlockId} {ls : LS} (h : ls.cur = some b) : Em b ls ls [] := by
  refine ⟨h, h, fun i => ?_, Nat.le_refl _, by simp [defIds]⟩
  by_cases hi : i = b
  · subst hi; cases hb : ls.blocks[i]? <;> simp
  · simp [hi]

theorem Em.trans {b : BlockId} {ls ls1 ls2 : LS} {E1 E2 : List Inst}
    (h1 : Em b ls ls1 E1) (h2 : Em b ls1 ls2 E2) : Em b ls ls2 (E1 ++ E2) := by
  refine ⟨h1.cur, h2.cur', fun i => ?_, Nat.le_trans h1.mono h2.mono, fun r hr => ?_⟩
  · rw [h2.blocks i, h1.blocks i]
    by_cases hi : i = b
    · subst hi
      cases hb : ls.blocks[i]? with
      | none => simp
      | some blk => simp [Array.append_assoc]
    · simp [hi]
  · simp only [defIds, List.filterMap_append, List.mem_append] at hr
    rcases hr with hr | hr
    · have := h1.fresh r (by simpa [defIds] using hr)
      exact ⟨this.1, Nat.lt_of_lt_of_le this.2 h2.mono⟩
    · have := h2.fresh r (by simpa [defIds] using hr)
      exact ⟨Nat.le_trans h1.mono this.1, this.2⟩

@[simp] theorem getThe_apply (le : LEnv) (ls : LS) : (getThe LS : B LS) le ls = (ls, ls) := rfl
@[simp] theorem readThe_apply (le : LEnv) (ls : LS) : (readThe LEnv : B LEnv) le ls = (le, ls) := rfl

theorem emitDef_em (op : Op) (le : LEnv) {ls : LS} {b : BlockId} (h : ls.cur = some b) :
    (emitDef op le ls).1 = ls.vals.size ∧ Em b ls (emitDef op le ls).2 [.def ls.vals.size op] := by
  unfold emitDef
  simp [h, bind, get, read, pure, modify, modifyGet, MonadStateOf.modifyGet, pushInst]
  refine ⟨h, rfl, fun i => ?_, by simp, fun r hr => ?_⟩
  · by_cases hi : i = b
    · subst hi; simp [Array.getElem?_modify]
    · simp [Array.getElem?_modify, hi, Ne.symm hi]
  · simp [defIds] at hr
    subst hr
    simp

theorem emitEffect_em (e : Effect) (le : LEnv) {ls : LS} {b : BlockId} (h : ls.cur = some b) :
    Em b ls (emitEffect e le ls).2 [.eff e] := by
  unfold emitEffect
  simp [h, bind, curBlock, get, read, pure, modify, modifyGet, MonadStateOf.modifyGet, pushInst]
  refine ⟨h, rfl, fun i => ?_, Nat.le_refl _, by simp [defIds]⟩
  by_cases hi : i = b
  · subst hi; simp [Array.getElem?_modify]
  · simp [Array.getElem?_modify, hi, Ne.symm hi]

/-! ### Frames -/

/-- The frame extends `fr`: every value defined there is defined here. -/
def Ext (fr fr' : Frame) : Prop :=
  ∀ (k : ValueId) (x : RVal), fr.vals[k]? = some x → fr'.vals[k]? = some x

theorem Ext.refl (fr : Frame) : Ext fr fr := fun _ _ h => h

theorem Ext.trans {a b c : Frame} (h1 : Ext a b) (h2 : Ext b c) : Ext a c :=
  fun k x h => h2 k x (h1 k x h)

/-- A Core environment and a frame, with the lowering state, correspond. -/
structure Rel (cfg : Cfg) (env : Env) (cx : FnCtx) (fr : Frame) (ls : LS) : Prop where
  prof : cx.cfg.profile = cfg.profile
  slots : cx.fn.slots = env.vars.mapIdx fun i lv => (⟨lv.ty, lv.kind, lv.scope, i⟩ : Slot)
  act : fr.act = env.act
  scopes : fr.scopes = env.scopes
  depth : fr.depth = env.depth
  below : ∀ k, fr.vals.contains k = true → k < ls.vals.size

/-- A computation that, when it yields a frame, yields `fr`. -/
def Keeps (fr : Frame) (m : M Frame) : Prop := ∀ s fr1 s1, m s = .ok fr1 s1 → fr1 = fr

theorem Keeps.pure (fr : Frame) : Keeps fr (pure fr) := by
  intro s fr1 s1 h
  rw [pure_apply] at h
  cases h
  rfl

theorem Keeps.bind {x : M α} {f : α → M Frame} {fr : Frame} (h : ∀ a, Keeps fr (f a)) :
    Keeps fr (x >>= f) := by
  intro s fr1 s1 hx
  rw [bind_apply] at hx
  cases hxs : x s with
  | stop e s2 => rw [hxs] at hx; cases hx
  | ok a s2 => rw [hxs] at hx; exact h a s2 fr1 s1 hx

theorem execEff_frame {fn : Func} {fr : Frame} {e : Effect}
    (he : EffPlain e) : Keeps fr (execEff fn fr e) := by
  cases e with
  | enter _ => exact absurd he (by simp [EffPlain])
  | leave _ => exact absurd he (by simp [EffPlain])
  | slotInit s v o =>
    simp only [execEff]
    repeat' first | exact Keeps.pure _ | refine Keeps.bind (fun _ => ?_)
  | store r v o =>
    simp only [execEff]
    repeat' first | exact Keeps.pure _ | refine Keeps.bind (fun _ => ?_)
  | append r v o =>
    simp only [execEff]
    repeat' first | exact Keeps.pure _ | refine Keeps.bind (fun _ => ?_)
  | print parts o =>
    simp only [execEff]
    repeat' first | exact Keeps.pure _ | refine Keeps.bind (fun _ => ?_)

/-- What running straight-line code without scope changes does to a frame. -/
theorem runS_inv {cx : FnCtx} : ∀ {E : List Inst} {fr fr' : Frame} {s s1 : St},
    NoScope E → runS cx fr E s = .ok fr' s1 →
    fr'.act = fr.act ∧ fr'.scopes = fr.scopes ∧ fr'.depth = fr.depth ∧
    (∀ (k : ValueId) (x : RVal), fr.vals[k]? = some x → k ∉ defIds E → fr'.vals[k]? = some x) ∧
    (∀ k, fr'.vals.contains k = true → fr.vals.contains k = true ∨ k ∈ defIds E)
  | [], fr, fr', s, s1, _, h => by
    simp only [runS, pure_apply] at h
    cases h
    exact ⟨rfl, rfl, rfl, fun _ _ h _ => h, fun k hk => Or.inl hk⟩
  | .def r op :: E, fr, fr', s, s1, hn, h => by
    have hn' : NoScope E := fun i hi => hn i (by simp [hi])
    simp only [runS, bind_apply] at h
    cases hx : execPure cx fr op s with
    | stop e s2 => rw [hx] at h; cases h
    | ok x s2 =>
      rw [hx] at h
      simp only [setCell, pure_apply] at h
      obtain ⟨ha, hs, hd, hv, hc⟩ := runS_inv (E := E) hn' h
      refine ⟨ha, hs, hd, fun k y hk hkd => ?_, fun k hk => ?_⟩
      · have hkr : k ≠ r := fun e => hkd (by simp [defIds, e])
        have hkE : k ∉ defIds E := fun e => hkd (by simp [defIds] at e ⊢; exact Or.inr e)
        refine hv k y ?_ hkE
        simp [Std.HashMap.getElem?_insert, hk, Ne.symm hkr]
      · rcases hc k hk with hc | hc
        · simp only [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at hc
          rcases hc with hc | hc
          · right; simp [defIds, hc]
          · exact Or.inl hc
        · right; simp [defIds] at hc ⊢; exact Or.inr hc
  | .eff e :: E, fr, fr', s, s1, hn, h => by
    have hn' : NoScope E := fun i hi => hn i (by simp [hi])
    have he : EffPlain e := hn (.eff e) (by simp)
    simp only [runS, bind_apply] at h
    cases hx : execEff cx.fn fr e s with
    | stop e s2 => rw [hx] at h; cases h
    | ok fr1 s2 =>
      rw [hx] at h
      have hk := execEff_frame (fn := cx.fn) (fr := fr) he s fr1 s2 hx
      subst hk
      obtain ⟨ha, hs, hd, hv, hc⟩ := runS_inv (E := E) hn' h
      refine ⟨ha, hs, hd, fun k y hk hkd => hv k y hk (by simpa [defIds] using hkd), fun k hk => ?_⟩
      rcases hc k hk with hc | hc
      · exact Or.inl hc
      · right; simpa [defIds] using hc
  | .term t :: E, fr, fr', s, s1, hn, h => by
    exact absurd (hn (.term t) (by simp)) (by simp [plainInst])

theorem runS_append (cx : FnCtx) : ∀ (E1 E2 : List Inst) (fr : Frame),
    runS cx fr (E1 ++ E2) = (runS cx fr E1 >>= fun fr1 => runS cx fr1 E2)
  | [], E2, fr => by simp [runS]
  | .def r op :: E1, E2, fr => by
    funext s
    simp only [List.cons_append, runS, bind_apply]
    cases execPure cx fr op s with
    | stop e s1 => rfl
    | ok x s1 =>
      simp only [setCell, pure_apply]
      exact congrFun (runS_append cx E1 E2 _) s1
  | .eff e :: E1, E2, fr => by
    funext s
    simp only [List.cons_append, runS, bind_apply]
    cases execEff cx.fn fr e s with
    | stop e s1 => rfl
    | ok x s1 => exact congrFun (runS_append cx E1 E2 _) s1
  | .term t :: E1, E2, fr => by
    funext s
    simp [runS, bind_apply]
    rfl

theorem rel_after {cfg : Cfg} {env : Env} {cx : FnCtx} {fr fr' : Frame} {ls ls' : LS}
    {b : BlockId} {E : List Inst} {s s1 : St}
    (hrel : Rel cfg env cx fr ls) (hem : Em b ls ls' E) (hn : NoScope E)
    (h : runS cx fr E s = .ok fr' s1) : Rel cfg env cx fr' ls' ∧ Ext fr fr' := by
  obtain ⟨ha, hs, hd, hv, hc⟩ := runS_inv hn h
  refine ⟨⟨hrel.prof, hrel.slots, ha.trans hrel.act, hs.trans hrel.scopes,
    hd.trans hrel.depth, fun k hk => ?_⟩, fun k x hk => ?_⟩
  · rcases hc k hk with hc | hc
    · exact Nat.lt_of_lt_of_le (hrel.below k hc) hem.mono
    · exact (hem.fresh k hc).2
  · have hk' : fr.vals.contains k = true := by
      simp [Std.HashMap.contains_eq_isSome_getElem?, hk]
    have hlt := hrel.below k hk'
    exact hv k x hk (fun hd => absurd (hem.fresh k hd).1 (Nat.not_le.mpr hlt))

/-- A fragment of the lowering: the builder action `x` is simulated by straight-line code,
for every Core run of `c`; the instructions do not depend on the run. `R` relates the
builder's result to the Core result in the frame afterwards. -/
def Claim (x : B α) (c : Nat → Cfg → Env → M γ) (R : α → γ → Frame → Prop) : Prop :=
  ∀ (le : LEnv) (ls : LS) (b : BlockId), ls.cur = some b →
    ∃ E, Em b ls (x le ls).2 E ∧ Straight E ∧ NoScope E ∧
      ∀ n cfg env cx fr, Rel cfg env cx fr ls →
        Sim (c n cfg env) (runS cx fr E)
          (fun v fr' => R (x le ls).1 v fr' ∧ Rel cfg env cx fr' (x le ls).2 ∧ Ext fr fr')

theorem Sim.strengthen {c : M α} {cx : FnCtx} {fr : Frame} {E : List Inst} {p : α → Frame → Prop}
    {Q : Frame → Prop} (h : Sim c (runS cx fr E) p)
    (hq : ∀ s fr' s1, runS cx fr E s = .ok fr' s1 → Q fr') :
    Sim c (runS cx fr E) (fun a fr' => p a fr' ∧ Q fr') := by
  intro s
  refine ⟨fun a s1 hc => ?_, (h s).2⟩
  obtain ⟨fr', hg, hp⟩ := (h s).1 a s1 hc
  exact ⟨fr', hg, hp, hq s fr' s1 hg⟩

/-- Build a claim from the instructions and a simulation that mentions only `R`. -/
theorem Claim.intro {x : B α} {c : Nat → Cfg → Env → M γ} {R : α → γ → Frame → Prop}
    (h : ∀ (le : LEnv) (ls : LS) (b : BlockId), ls.cur = some b →
      ∃ E, Em b ls (x le ls).2 E ∧ Straight E ∧ NoScope E ∧
        ∀ n cfg env cx fr, Rel cfg env cx fr ls →
          Sim (c n cfg env) (runS cx fr E) (fun v fr' => R (x le ls).1 v fr')) :
    Claim x c R := by
  intro le ls b hb
  obtain ⟨E, hem, hs, hn, hsim⟩ := h le ls b hb
  refine ⟨E, hem, hs, hn, fun n cfg env cx fr hrel => ?_⟩
  exact (hsim n cfg env cx fr hrel).strengthen (Q := fun fr' => Rel cfg env cx fr' (x le ls).2 ∧ Ext fr fr')
    (fun s fr' s1 hr => rel_after hrel hem hn hr)

theorem Sim.timeout {g : M Frame} {p : α → Frame → Prop} : Sim (Goose.Core.timeout : M α) g p := by
  intro s
  refine ⟨fun a s1 h => ?_, fun e s1 h hf => ?_⟩
  · simp [Goose.Core.timeout, M.stop] at h
  · simp [Goose.Core.timeout, M.stop] at h
    obtain ⟨rfl, _⟩ := h
    exact absurd hf (by simp [IsFinal])

theorem Sim.expectInt {va : Val} {f : IntTy × Int → M α} {g : M Frame} {p : α → Frame → Prop}
    (h : ∀ t x, va = .int t x → Sim (f (t, x)) g p) : Sim (expectInt va >>= f) g p := by
  cases va with
  | int t x => exact h t x rfl
  | _ =>
    intro s
    refine ⟨fun a s1 hc => ?_, fun e s1 hc hf => ?_⟩
    · simp [Goose.Core.expectInt, fault, M.stop, bind_apply] at hc
    · simp [Goose.Core.expectInt, fault, M.stop, bind_apply] at hc
      obtain ⟨rfl, _⟩ := hc
      exact absurd hf (by simp [IsFinal])

theorem Sim.expectBool {va : Val} {f : Bool → M α} {g : M Frame} {p : α → Frame → Prop}
    (h : ∀ b, va = .bool b → Sim (f b) g p) : Sim (expectBool va >>= f) g p := by
  cases va with
  | bool b => exact h b rfl
  | _ =>
    intro s
    refine ⟨fun a s1 hc => ?_, fun e s1 hc hf => ?_⟩
    · simp [Goose.Core.expectBool, fault, M.stop, bind_apply] at hc
    · simp [Goose.Core.expectBool, fault, M.stop, bind_apply] at hc
      obtain ⟨rfl, _⟩ := hc
      exact absurd hf (by simp [IsFinal])

theorem getCell_of {fr : Frame} {k : ValueId} {x : RVal} (h : fr.vals[k]? = some x) :
    getCell fr k = pure x := by
  unfold getCell; rw [h]

theorem getVal_of {fr : Frame} {k : ValueId} {v : Val} (h : fr.vals[k]? = some (.val v)) :
    getVal fr k = pure v := by
  unfold getVal; rw [getCell_of h]; rfl

theorem getView_of {fr : Frame} {k : ValueId} {vw : ViewVal} (h : fr.vals[k]? = some (.view vw)) :
    getView fr k = pure vw := by
  unfold getView; rw [getCell_of h]; rfl

theorem cell_insert (fr : Frame) (r : ValueId) (x : RVal) :
    ({ fr with vals := fr.vals.insert r x } : Frame).vals[r]? = some x := by
  simp [Std.HashMap.getElem?_insert]

/-- A defining instruction whose operation computes what `c` does. -/
theorem Sim.def_leaf {cx : FnCtx} {fr : Frame} {r : ValueId} {op : Op} {c : M α} (inj : α → RVal)
    (hx : execPure cx fr op = c >>= fun a => pure (inj a)) :
    Sim c (runS cx fr [.def r op]) (fun a fr' => fr'.vals[r]? = some (inj a)) := by
  intro s
  have key : ∀ s', runS cx fr [.def r op] s' =
      (match c s' with
       | .ok a s1 => .ok { fr with vals := fr.vals.insert r (inj a) } s1
       | .stop e s1 => .stop e s1) := by
    intro s'
    simp only [runS, bind_apply, hx]
    cases c s' with
    | stop e s1 => rfl
    | ok a s1 => rfl
  refine ⟨fun a s1 hc => ?_, fun e s1 hc _ => ?_⟩
  · rw [key s, hc]
    exact ⟨_, rfl, cell_insert fr r _⟩
  · rw [key s, hc]

/-- An effect that computes what `c` does and leaves the frame alone. -/
theorem Sim.eff_leaf {cx : FnCtx} {fr : Frame} {e : Effect} {c : M α}
    (hx : execEff cx.fn fr e = c >>= fun _ => pure fr) :
    Sim c (runS cx fr [.eff e]) (fun _ fr' => fr' = fr) := by
  intro s
  have key : ∀ s', runS cx fr [.eff e] s' =
      (match c s' with
       | .ok _ s1 => .ok fr s1
       | .stop e s1 => .stop e s1) := by
    intro s'
    simp only [runS, bind_apply, hx]
    cases c s' with
    | stop e s1 => rfl
    | ok a s1 => rfl
  refine ⟨fun a s1 hc => ?_, fun e s1 hc _ => ?_⟩
  · rw [key s, hc]
    exact ⟨_, rfl, rfl⟩
  · rw [key s, hc]

theorem straight_def (r : ValueId) {op : Op} (h : ∀ f a o, op ≠ .call f a o) :
    Straight [.def r op] := by
  intro i hi
  simp only [List.mem_singleton] at hi
  subst hi
  cases op with
  | call f a o => exact absurd rfl (h f a o)
  | _ => trivial

theorem straight_eff (e : Effect) : Straight [.eff e] := by
  intro i hi
  simp only [List.mem_singleton] at hi
  subst hi
  trivial

/-- A claim for one instruction that has no operand. -/
theorem Claim.def0 {op : Op} {c : Nat → Cfg → Env → M γ} (inj : γ → RVal)
    (hnc : ∀ f a o, op ≠ .call f a o)
    (hz : ∀ cfg env, c 0 cfg env = Goose.Core.timeout)
    (hx : ∀ n cfg env cx fr ls', Rel cfg env cx fr ls' →
      execPure cx fr op = c (n + 1) cfg env >>= fun a => pure (inj a)) :
    Claim (emitDef op) c (fun r v fr => fr.vals[r]? = some (inj v)) := by
  apply Claim.intro
  intro le ls b hb
  obtain ⟨h1, h2⟩ := emitDef_em op le hb
  refine ⟨_, h2, ?_, ?_, fun n cfg env cx fr hrel => ?_⟩
  · exact straight_def _ hnc
  · simp [NoScope, plainInst]
  · rw [h1]
    cases n with
    | zero => rw [hz]; exact Sim.timeout
    | succ n => exact Sim.def_leaf inj (hx n cfg env cx fr ls hrel)

/-! ### The fragment -/

mutual
/-- Expressions the proof covers: no short-circuit, no `if` or block value, no call. -/
def exprA : Expr → Bool
  | .lit .. | .bool _ => true
  | .read p => placeA p
  | .ref _ p => placeA p
  | .slice _ v lo hi _ => viewA v && boundA lo && boundA hi
  | .len v => viewA v
  | .un _ e _ => exprA e
  | .bin _ a b _ => exprA a && exprA b
  | .cmp _ a b => exprA a && exprA b
  | .and .. | .or .. => false
  | .not e => exprA e
  | .conv _ _ e _ => exprA e
  | .call .. => false
  | .push p e => placeA p && exprA e
  | .ifE .. | .blockE _ => false
  | .arrLit _ es => exprsA es
  | .fill _ e => exprA e

def exprsA : List Expr → Bool
  | [] => true
  | e :: es => exprA e && exprsA es

def placeA : Place → Bool
  | .var _ | .global _ => true
  | .deref e => exprA e
  | .elem v i _ => viewA v && exprA i

def viewA : View → Bool
  | .of p => placeA p
  | .val e => exprA e

def boundA : Bound → Bool
  | .omitted => true
  | .expr e | .fromEnd e => exprA e
end

theorem slots_get {cfg : Cfg} {env : Env} {cx : FnCtx} {fr : Frame} {ls : LS}
    (hrel : Rel cfg env cx fr ls) (x : Nat) :
    cx.fn.slots[x]? = env.vars[x]?.map fun lv => (⟨lv.ty, lv.kind, lv.scope, x⟩ : Slot) := by
  rw [hrel.slots]
  simp [Array.getElem?_mapIdx]

theorem slotRoot_eq {cfg : Cfg} {env : Env} {cx : FnCtx} {fr : Frame} {ls : LS}
    (hrel : Rel cfg env cx fr ls) (x : Nat) : slotRoot cx.fn fr x = rootOf env x := by
  unfold slotRoot rootOf
  rw [slots_get hrel x]
  cases env.vars[x]? with
  | none => rfl
  | some lv =>
    simp only [Option.map_some, hrel.scopes, hrel.act]
    cases List.lookup lv.scope env.scopes <;> rfl

theorem B.bind_run (x : B α) (f : α → B β) (le : LEnv) (ls : LS) :
    (x >>= f) le ls = f (x le ls).1 le (x le ls).2 := rfl

theorem B.pure_run (a : α) (le : LEnv) (ls : LS) : (pure a : B α) le ls = (a, ls) := rfl

theorem valTy_state (v : ValueId) (le : LEnv) (ls : LS) : (valTy v le ls).2 = ls := by
  unfold valTy; simp [bind, get, pure]
  cases ls.vals[v]? with
  | none => rfl
  | some o => cases o <;> rfl

theorem intTyOf_state (v : ValueId) (le : LEnv) (ls : LS) : (intTyOf v le ls).2 = ls := by
  unfold intTyOf
  simp only [B.bind_run, valTy_state]
  cases (valTy v le ls).1 with
  | data t => cases t <;> rfl
  | view _ _ => rfl

theorem Sim.expectSameTy {t u : IntTy} {f : Unit → M α} {g : M Frame} {p : α → Frame → Prop}
    (h : t = u → Sim (f ()) g p) : Sim (expectSameTy t u >>= f) g p := by
  by_cases htu : t = u
  · subst htu
    simp only [Goose.Core.expectSameTy, if_true]
    exact h rfl
  · intro s
    refine ⟨fun a s1 hc => ?_, fun e s1 hc hf => ?_⟩
    · simp [Goose.Core.expectSameTy, htu, fault, M.stop, bind_apply] at hc
    · simp [Goose.Core.expectSameTy, htu, fault, M.stop, bind_apply] at hc
      obtain ⟨rfl, _⟩ := hc
      exact absurd hf (by simp [IsFinal])

theorem Sim.expectRef {va : Val} {f : Loc → M α} {g : M Frame} {p : α → Frame → Prop}
    (h : ∀ l, va = .ref l → Sim (f l) g p) : Sim (expectRef va >>= f) g p := by
  cases va with
  | ref l => exact h l rfl
  | _ =>
    intro s
    refine ⟨fun a s1 hc => ?_, fun e s1 hc hf => ?_⟩
    · simp [Goose.Core.expectRef, fault, M.stop, bind_apply] at hc
    · simp [Goose.Core.expectRef, fault, M.stop, bind_apply] at hc
      obtain ⟨rfl, _⟩ := hc
      exact absurd hf (by simp [IsFinal])

theorem Sim.of_bind_pure {c : M α} {g : M Frame} {p : α → Frame → Prop}
    (h : Sim c (g >>= fun fr => pure fr) p) : Sim c g p := by
  simpa using h

/-- A binary operation on cells holding integers of one type. -/
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

theorem Straight.append {E1 E2 : List Inst} (h1 : Straight E1) (h2 : Straight E2) :
    Straight (E1 ++ E2) := by
  intro i hi
  rcases List.mem_append.mp hi with h | h
  · exact h1 i h
  · exact h2 i h

theorem NoScope.append {E1 E2 : List Inst} (h1 : NoScope E1) (h2 : NoScope E2) :
    NoScope (E1 ++ E2) := by
  intro i hi
  rcases List.mem_append.mp hi with h | h
  · exact h1 i h
  · exact h2 i h

theorem noscope_def (r : ValueId) (op : Op) : NoScope [.def r op] := by
  intro i hi
  simp only [List.mem_singleton] at hi
  subst hi
  trivial

theorem noscope_eff {e : Effect} (h : EffPlain e) : NoScope [.eff e] := by
  intro i hi
  simp only [List.mem_singleton] at hi
  subst hi
  exact h

/-- What a lowered bound stands for: the integer it denotes in the frame. -/
def BndRel (fr : Frame) (len : Nat) (dflt : Int) : Bnd → Int → Prop
  | .omitted, k => k = dflt
  | .val v, k => ∃ t, fr.vals[v]? = some (.val (.int t k))
  | .fromEnd v, k => ∃ t kk, fr.vals[v]? = some (.val (.int t kk)) ∧ k = (len : Int) - kk

theorem BndRel.ext {fr fr' : Frame} (h : Ext fr fr') {len : Nat} {dflt : Int} {bnd : Bnd} {k : Int}
    (hr : BndRel fr len dflt bnd k) : BndRel fr' len dflt bnd k := by
  cases bnd with
  | omitted => exact hr
  | val v => obtain ⟨t, ht⟩ := hr; exact ⟨t, h _ _ ht⟩
  | fromEnd v => obtain ⟨t, kk, ht, hk⟩ := hr; exact ⟨t, kk, h _ _ ht, hk⟩

theorem evalBnd_of {fr : Frame} {len : Nat} {dflt : Int} {bnd : Bnd} {k : Int}
    (h : BndRel fr len dflt bnd k) : evalBnd fr len dflt bnd = pure k := by
  cases bnd with
  | omitted => simp only [BndRel] at h; subst h; rfl
  | val v =>
    obtain ⟨t, ht⟩ := h
    simp only [evalBnd, getVal_of ht, Goose.Core.expectInt, pure_bind]
  | fromEnd v =>
    obtain ⟨t, kk, ht, hk⟩ := h
    subst hk
    simp only [evalBnd, getVal_of ht, Goose.Core.expectInt, pure_bind]

/-- The values the cells hold, in order. -/
def Cells (fr : Frame) : List ValueId → List Val → Prop
  | [], [] => True
  | i :: is, v :: vs => fr.vals[i]? = some (.val v) ∧ Cells fr is vs
  | _, _ => False

theorem Cells.ext {fr fr' : Frame} (h : Ext fr fr') :
    ∀ {ids : List ValueId} {vs : List Val}, Cells fr ids vs → Cells fr' ids vs
  | [], [], _ => trivial
  | i :: is, v :: vs, ⟨h1, h2⟩ => ⟨h _ _ h1, Cells.ext h h2⟩
  | [], _ :: _, hc => absurd hc (by simp [Cells])
  | _ :: _, [], hc => absurd hc (by simp [Cells])

theorem mapList_getVal_of {fr : Frame} :
    ∀ {ids : List ValueId} {vs : List Val}, Cells fr ids vs → mapList (getVal fr) ids = pure vs
  | [], [], _ => rfl
  | i :: is, v :: vs, ⟨h1, h2⟩ => by
    simp only [mapList, getVal_of h1, pure_bind, mapList_getVal_of h2]
  | [], _ :: _, hc => absurd hc (by simp [Cells])
  | _ :: _, [], hc => absurd hc (by simp [Cells])

theorem Sim.expectRef' {va : Val} {g : M Frame} {p : Loc → Frame → Prop}
    (h : ∀ l, va = .ref l → Sim (pure l) g p) : Sim (Goose.Core.expectRef va) g p := by
  have := Sim.expectRef (f := pure) (g := g) (p := p) h
  simpa using this

theorem freezeTo_eq (m : Mutability) (r : ValueId) (le : LEnv) (ls : LS) :
    freezeTo m r le ls = (r, ls) ∨ freezeTo m r le ls = emitDef (.refFreeze r) le ls := by
  unfold freezeTo
  simp only [B.bind_run, valTy_state]
  generalize (valTy r le ls).1 = vt
  cases m <;> cases vt with
  | view _ _ => first | (left; rfl) | (right; rfl)
  | data t =>
    cases t with
    | ref m' t' => cases m' <;> first | (left; rfl) | (right; rfl)
    | _ => first | (left; rfl) | (right; rfl)

theorem Sim.expectSlice {va : Val} {f : Loc × Nat × Nat → M α} {g : M Frame} {p : α → Frame → Prop}
    (h : ∀ l st n, va = .slice l st n → Sim (f (l, st, n)) g p) :
    Sim (Goose.Core.expectSlice va >>= f) g p := by
  cases va with
  | slice l st n => exact h l st n rfl
  | _ =>
    intro s
    refine ⟨fun a s1 hc => ?_, fun e s1 hc hf => ?_⟩
    · simp [Goose.Core.expectSlice, fault, M.stop, bind_apply] at hc
    · simp [Goose.Core.expectSlice, fault, M.stop, bind_apply] at hc
      obtain ⟨rfl, _⟩ := hc
      exact absurd hf (by simp [IsFinal])

theorem Sim.expectIntTy {t : Ty} {f : IntTy → M α} {g : M Frame} {p : α → Frame → Prop}
    (h : ∀ d, t = .int d → Sim (f d) g p) : Sim (Goose.Core.expectIntTy t >>= f) g p := by
  cases t with
  | int d => exact h d rfl
  | _ =>
    intro s
    refine ⟨fun a s1 hc => ?_, fun e s1 hc hf => ?_⟩
    · simp [Goose.Core.expectIntTy, fault, M.stop, bind_apply] at hc
    · simp [Goose.Core.expectIntTy, fault, M.stop, bind_apply] at hc
      obtain ⟨rfl, _⟩ := hc
      exact absurd hf (by simp [IsFinal])

theorem Sim.expectFixedCount {t : Ty} {f : Nat → M α} {g : M Frame} {p : α → Frame → Prop}
    (h : ∀ e k, t = .arr e k → Sim (f k) g p) : Sim (Goose.Core.expectFixedCount t >>= f) g p := by
  cases t with
  | arr e k => exact h e k rfl
  | _ =>
    intro s
    refine ⟨fun a s1 hc => ?_, fun e s1 hc hf => ?_⟩
    · simp [Goose.Core.expectFixedCount, fault, M.stop, bind_apply] at hc
    · simp [Goose.Core.expectFixedCount, fault, M.stop, bind_apply] at hc
      obtain ⟨rfl, _⟩ := hc
      exact absurd hf (by simp [IsFinal])

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

/-- A claim for a lowered bound: the instructions do not depend on the length and
default the bound is read against. -/
def BoundClaim (bd : Bound) : Prop :=
  ∀ (le : LEnv) (ls : LS) (b : BlockId), ls.cur = some b →
    ∃ E, Em b ls (lowerBound bd le ls).2 E ∧ Straight E ∧ NoScope E ∧
      ∀ len dflt n cfg env cx fr, Rel cfg env cx fr ls →
        Sim (evalBound n cfg env len dflt bd) (runS cx fr E)
          (fun k fr' => BndRel fr' len dflt (lowerBound bd le ls).1 k ∧
            Rel cfg env cx fr' (lowerBound bd le ls).2 ∧ Ext fr fr')

theorem BoundClaim.intro {bd : Bound}
    (h : ∀ (le : LEnv) (ls : LS) (b : BlockId), ls.cur = some b →
      ∃ E, Em b ls (lowerBound bd le ls).2 E ∧ Straight E ∧ NoScope E ∧
        ∀ len dflt n cfg env cx fr, Rel cfg env cx fr ls →
          Sim (evalBound n cfg env len dflt bd) (runS cx fr E)
            (fun k fr' => BndRel fr' len dflt (lowerBound bd le ls).1 k)) :
    BoundClaim bd := by
  intro le ls b hb
  obtain ⟨E, hem, hs, hn, hsim⟩ := h le ls b hb
  refine ⟨E, hem, hs, hn, fun len dflt n cfg env cx fr hrel => ?_⟩
  exact (hsim len dflt n cfg env cx fr hrel).strengthen
    (Q := fun fr' => Rel cfg env cx fr' (lowerBound bd le ls).2 ∧ Ext fr fr')
    (fun s fr' s1 hr => rel_after hrel hem hn hr)

/-- The target of a conversion, or the source when it is not an integer type. -/
def convDst (target : Ty) (src : IntTy) : IntTy :=
  match target with
  | .int d => d
  | _ => src

theorem lowerExpr_conv (k : ConvKind) (target : Ty) (a : Expr) (org : OriginId) :
    lowerExpr (.conv k target a org) =
      lowerExpr a >>= fun x => intTyOf x >>= fun src =>
        emitDef (.conv k src (convDst target src) x (some org)) := by
  simp only [lowerExpr]
  rfl

mutual
theorem placeClaim : ∀ (p : Place), placeA p = true →
    Claim (lowerPlace p) (fun n cfg env => evalPlace n cfg env p)
      (fun r l fr => fr.vals[r]? = some (.val (.ref l)))
  | .var x, _ => by
    simp only [lowerPlace]
    refine Claim.def0 (fun l => .val (.ref l)) (by simp) (fun _ _ => by simp [evalPlace])
      fun n cfg env cx fr ls' hrel => ?_
    simp only [evalPlace, execPure, slotRoot_eq hrel, bind_assoc, pure_bind]
  | .global g, _ => by
    simp only [lowerPlace]
    exact Claim.def0 (fun l => .val (.ref l)) (by simp) (fun _ _ => by simp [evalPlace])
      fun n cfg env cx fr ls' hrel => by simp [evalPlace, execPure]
  | .deref e, h => by
    have he := exprClaim e (by simpa [placeA] using h)
    simp only [lowerPlace]
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨E, hEm, hS, hN, hs⟩ := he le ls bb hcur
    refine ⟨E, hEm, hS, hN, fun n cfg env cx fr hrel => ?_⟩
    cases n with
    | zero => simp only [evalPlace]; exact Sim.timeout
    | succ n =>
      simp only [evalPlace]
      refine Sim.of_bind_pure (Sim.bind (hs n cfg env cx fr hrel) fun v fr1 ⟨hc, _, _⟩ => ?_)
      refine Sim.expectRef' fun l hv => ?_
      subst hv
      exact Sim.pure' rfl hc
  | .elem v i org, h => by
    have hv := viewClaim v (by simp [placeA] at h; exact h.1)
    have hi := exprClaim i (by simp [placeA] at h; exact h.2)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Ev, hEmv, hSv, hNv, hsv⟩ := hv le ls bb hcur
    obtain ⟨Ei, hEmi, hSi, hNi, hsi⟩ := hi le (lowerView v le ls).2 bb hEmv.cur'
    simp only [lowerPlace, B.bind_run]
    obtain ⟨hr, hEmc⟩ := emitDef_em (.indexChecked (lowerView v le ls).1
      (lowerExpr i le (lowerView v le ls).2).1 (some org)) le hEmi.cur'
    refine ⟨Ev ++ (Ei ++ _), hEmv.trans (hEmi.trans hEmc),
      hSv.append (hSi.append (straight_def _ (by simp))),
      hNv.append (hNi.append (noscope_def _ _)), fun n cfg env cx fr hrel => ?_⟩
    rw [hr]
    cases n with
    | zero => simp only [evalPlace]; exact Sim.timeout
    | succ n =>
      simp only [evalPlace, runS_append]
      refine Sim.bind (hsv n cfg env cx fr hrel) fun vw fr1 ⟨hcv, hrel1, hext1⟩ => ?_
      refine Sim.bind (hsi n cfg env cx fr1 hrel1) fun va fr2 ⟨hci, hrel2, hext2⟩ => ?_
      refine Sim.expectInt fun t k hva => ?_
      subst hva
      refine Sim.def_leaf (c := _) (fun l => RVal.val (.ref l)) ?_
      simp only [execPure, getView_of (hext2 _ _ hcv), getVal_of hci, Goose.Core.expectInt,
        bind_assoc, pure_bind]
      by_cases hk : 0 ≤ k ∧ k < (vw.len : Int)
      · simp [hk]
      · simp [hk, abortAtOrg, abortAt, M.stop, bind_apply]
        rfl

theorem viewClaim : ∀ (v : View), viewA v = true →
    Claim (lowerView v) (fun n cfg env => evalView n cfg env v)
      (fun r vw fr => fr.vals[r]? = some (.view vw))
  | .of p, h => by
    have hp := placeClaim p (by simpa [viewA] using h)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Ep, hEmp, hSp, hNp, hsp⟩ := hp le ls bb hcur
    simp only [lowerView, B.bind_run]
    obtain ⟨hr, hEmc⟩ := emitDef_em (.snapshot (lowerPlace p le ls).1) le hEmp.cur'
    refine ⟨Ep ++ _, hEmp.trans hEmc, hSp.append (straight_def _ (by simp)),
      hNp.append (noscope_def _ _), fun n cfg env cx fr hrel => ?_⟩
    rw [hr]
    cases n with
    | zero => simp only [evalView]; exact Sim.timeout
    | succ n =>
      simp only [evalView, runS_append]
      refine Sim.bind (hsp n cfg env cx fr hrel) fun l fr1 ⟨hc, hrel1, hext1⟩ => ?_
      exact Sim.def_leaf RVal.view
        (by simp only [execPure, getVal_of hc, Goose.Core.expectRef, bind_assoc, pure_bind])
  | .val e, h => by
    have he := exprClaim e (by simpa [viewA] using h)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Ee, hEme, hSe, hNe, hse⟩ := he le ls bb hcur
    simp only [lowerView, B.bind_run]
    obtain ⟨hr, hEmc⟩ := emitDef_em (.sliceView (lowerExpr e le ls).1) le hEme.cur'
    refine ⟨Ee ++ _, hEme.trans hEmc, hSe.append (straight_def _ (by simp)),
      hNe.append (noscope_def _ _), fun n cfg env cx fr hrel => ?_⟩
    rw [hr]
    cases n with
    | zero => simp only [evalView]; exact Sim.timeout
    | succ n =>
      simp only [evalView, runS_append]
      refine Sim.bind (hse n cfg env cx fr hrel) fun v fr1 ⟨hc, hrel1, hext1⟩ => ?_
      refine Sim.expectSlice fun l st len hv => ?_
      subst hv
      exact Sim.def_leaf RVal.view
        (by simp only [execPure, getVal_of hc, Goose.Core.expectSlice, bind_assoc, pure_bind])

theorem boundClaim : ∀ (bd : Bound), boundA bd = true → BoundClaim bd
  | .omitted, _ => by
    apply BoundClaim.intro
    intro le ls bb hcur
    simp only [lowerBound]
    refine ⟨[], ?_, by simp [Straight], by simp [NoScope], fun len dflt n cfg env cx fr hrel => ?_⟩
    · simpa [B.pure_run] using Em.refl hcur
    · cases n with
      | zero => simp only [evalBound]; exact Sim.timeout
      | succ n =>
        simp only [evalBound]
        exact Sim.pure' rfl rfl
  | .expr e, h => by
    have he := exprClaim e (by simpa [boundA] using h)
    apply BoundClaim.intro
    intro le ls bb hcur
    obtain ⟨Ee, hEme, hSe, hNe, hse⟩ := he le ls bb hcur
    simp only [lowerBound, B.bind_run, B.pure_run]
    refine ⟨Ee, hEme, hSe, hNe, fun len dflt n cfg env cx fr hrel => ?_⟩
    cases n with
    | zero => simp only [evalBound]; exact Sim.timeout
    | succ n =>
      simp only [evalBound]
      refine Sim.of_bind_pure (Sim.bind (hse n cfg env cx fr hrel) fun v fr1 ⟨hc, _, _⟩ => ?_)
      refine Sim.expectInt fun t k hv => ?_
      subst hv
      exact Sim.pure' rfl ⟨t, hc⟩
  | .fromEnd e, h => by
    have he := exprClaim e (by simpa [boundA] using h)
    apply BoundClaim.intro
    intro le ls bb hcur
    obtain ⟨Ee, hEme, hSe, hNe, hse⟩ := he le ls bb hcur
    simp only [lowerBound, B.bind_run, B.pure_run]
    refine ⟨Ee, hEme, hSe, hNe, fun len dflt n cfg env cx fr hrel => ?_⟩
    cases n with
    | zero => simp only [evalBound]; exact Sim.timeout
    | succ n =>
      simp only [evalBound]
      refine Sim.of_bind_pure (Sim.bind (hse n cfg env cx fr hrel) fun v fr1 ⟨hc, _, _⟩ => ?_)
      refine Sim.expectInt fun t k hv => ?_
      subst hv
      exact Sim.pure' rfl ⟨t, k, hc, rfl⟩

theorem exprsClaim : ∀ (es : List Expr), exprsA es = true →
    Claim (lowerExprs es) (fun n cfg env => mapList (evalExpr n cfg env) es)
      (fun ids vs fr => Cells fr ids vs)
  | [], _ => by
    apply Claim.intro
    intro le ls bb hcur
    simp only [lowerExprs, B.pure_run]
    refine ⟨[], by simpa using Em.refl hcur, by simp [Straight], by simp [NoScope],
      fun n cfg env cx fr hrel => ?_⟩
    simp only [mapList]
    exact Sim.pure' rfl trivial
  | e :: es, h => by
    have he := exprClaim e (by simp [exprsA] at h; exact h.1)
    have hes := exprsClaim es (by simp [exprsA] at h; exact h.2)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Ee, hEme, hSe, hNe, hse⟩ := he le ls bb hcur
    obtain ⟨Es, hEms, hSs, hNs, hss⟩ := hes le (lowerExpr e le ls).2 bb hEme.cur'
    simp only [lowerExprs, B.bind_run, B.pure_run]
    refine ⟨Ee ++ Es, hEme.trans hEms, hSe.append hSs, hNe.append hNs, fun n cfg env cx fr hrel => ?_⟩
    simp only [mapList, runS_append]
    refine Sim.bind (hse n cfg env cx fr hrel) fun v fr1 ⟨hc, hrel1, hext1⟩ => ?_
    refine Sim.of_bind_pure (Sim.bind (hss n cfg env cx fr1 hrel1) fun vs fr2 ⟨hcs, hrel2, hext2⟩ => ?_)
    exact Sim.pure' rfl ⟨hext2 _ _ hc, hcs⟩

theorem exprClaim : ∀ (e : Expr), exprA e = true →
    Claim (lowerExpr e) (fun n cfg env => evalExpr n cfg env e) (fun r v fr => fr.vals[r]? = some (.val v))
  | .lit t k, _ => by
    simp only [lowerExpr]
    exact Claim.def0 (fun v => .val v) (by simp) (fun _ _ => by simp [evalExpr])
      fun n cfg env cx fr ls' hrel => by simp [evalExpr, execPure]
  | .bool b, _ => by
    simp only [lowerExpr]
    exact Claim.def0 (fun v => .val v) (by simp) (fun _ _ => by simp [evalExpr])
      fun n cfg env cx fr ls' hrel => by simp [evalExpr, execPure]
  | .bin op a b org, h => by
    have ha := exprClaim a (by simp [exprA] at h; exact h.1)
    have hb := exprClaim b (by simp [exprA] at h; exact h.2)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Ea, hEma, hSa, hNa, hsa⟩ := ha le ls bb hcur
    obtain ⟨Eb, hEmb, hSb, hNb, hsb⟩ := hb le (lowerExpr a le ls).2 bb hEma.cur'
    simp only [lowerExpr, B.bind_run]
    rw [intTyOf_state]
    obtain ⟨hr, hEmc⟩ := emitDef_em (.bin op (intTyOf (lowerExpr a le ls).1 le (lowerExpr b le (lowerExpr a le ls).2).2).1 (lowerExpr a le ls).1 (lowerExpr b le (lowerExpr a le ls).2).1 (some org)) le hEmb.cur'
    refine ⟨Ea ++ (Eb ++ _), hEma.trans (hEmb.trans hEmc), hSa.append (hSb.append (straight_def _ (by simp))),
      hNa.append (hNb.append (noscope_def _ _)), fun n cfg env cx fr hrel => ?_⟩
    rw [hr]
    cases n with
    | zero => simp only [evalExpr]; exact Sim.timeout
    | succ n =>
      simp only [evalExpr]
      simp only [runS_append]
      refine Sim.bind (hsa n cfg env cx fr hrel) fun va fr1 ⟨hca, hrel1, hext1⟩ => ?_
      refine Sim.expectInt fun t0 x0 hva => ?_
      subst hva
      refine Sim.bind (hsb n cfg env cx fr1 hrel1) fun vb fr2 ⟨hcb, hrel2, hext2⟩ => ?_
      refine Sim.expectInt fun u y hvb => ?_
      subst hvb
      refine Sim.expectSameTy fun htu => ?_
      subst htu
      exact Sim.def_leaf RVal.val (execPure_bin hrel2.prof (hext2 _ _ hca) hcb)
  | .read p, h => by
    have hp := placeClaim p (by simpa [exprA] using h)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Ep, hEmp, hSp, hNp, hsp⟩ := hp le ls bb hcur
    simp only [lowerExpr, B.bind_run]
    obtain ⟨hr, hEmc⟩ := emitDef_em (.load (lowerPlace p le ls).1) le hEmp.cur'
    refine ⟨Ep ++ _, hEmp.trans hEmc, hSp.append (straight_def _ (by simp)),
      hNp.append (noscope_def _ _), fun n cfg env cx fr hrel => ?_⟩
    rw [hr]
    cases n with
    | zero => simp only [evalExpr]; exact Sim.timeout
    | succ n =>
      simp only [evalExpr, runS_append]
      refine Sim.bind (hsp n cfg env cx fr hrel) fun l fr1 ⟨hc, hrel1, hext1⟩ => ?_
      exact Sim.def_leaf RVal.val
        (by simp only [execPure, getVal_of hc, Goose.Core.expectRef, bind_assoc, pure_bind])
  | .ref m p, h => by
    have hp := placeClaim p (by simpa [exprA] using h)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Ep, hEmp, hSp, hNp, hsp⟩ := hp le ls bb hcur
    simp only [lowerExpr, B.bind_run]
    rcases freezeTo_eq m (lowerPlace p le ls).1 le (lowerPlace p le ls).2 with hf | hf
    · rw [hf]
      refine ⟨Ep, hEmp, hSp, hNp, fun n cfg env cx fr hrel => ?_⟩
      cases n with
      | zero => simp only [evalExpr]; exact Sim.timeout
      | succ n =>
        simp only [evalExpr]
        refine Sim.of_bind_pure (Sim.bind (hsp n cfg env cx fr hrel) fun l fr1 ⟨hc, _, _⟩ => ?_)
        exact Sim.pure' rfl hc
    · rw [hf]
      obtain ⟨hr, hEmc⟩ := emitDef_em (.refFreeze (lowerPlace p le ls).1) le hEmp.cur'
      refine ⟨Ep ++ _, hEmp.trans hEmc, hSp.append (straight_def _ (by simp)),
        hNp.append (noscope_def _ _), fun n cfg env cx fr hrel => ?_⟩
      rw [hr]
      cases n with
      | zero => simp only [evalExpr]; exact Sim.timeout
      | succ n =>
        simp only [evalExpr, runS_append]
        refine Sim.bind (hsp n cfg env cx fr hrel) fun l fr1 ⟨hc, hrel1, hext1⟩ => ?_
        exact Sim.def_leaf RVal.val
          (by simp only [execPure, getVal_of hc, Goose.Core.expectRef, bind_assoc, pure_bind])
  | .slice m v lo hi org, h => by
    have hv := viewClaim v (by simp [exprA] at h; exact h.1.1)
    have hl := boundClaim lo (by simp [exprA] at h; exact h.1.2)
    have hh := boundClaim hi (by simp [exprA] at h; exact h.2)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Ev, hEmv, hSv, hNv, hsv⟩ := hv le ls bb hcur
    obtain ⟨El, hEml, hSl, hNl, hsl⟩ := hl le (lowerView v le ls).2 bb hEmv.cur'
    obtain ⟨Eh, hEmh, hSh, hNh, hsh⟩ := hh le (lowerBound lo le (lowerView v le ls).2).2 bb hEml.cur'
    simp only [lowerExpr, B.bind_run]
    obtain ⟨hr, hEmc⟩ := emitDef_em (.viewSlice m (lowerView v le ls).1
      (lowerBound lo le (lowerView v le ls).2).1
      (lowerBound hi le (lowerBound lo le (lowerView v le ls).2).2).1 (some org)) le hEmh.cur'
    refine ⟨Ev ++ (El ++ (Eh ++ _)), hEmv.trans (hEml.trans (hEmh.trans hEmc)),
      hSv.append (hSl.append (hSh.append (straight_def _ (by simp)))),
      hNv.append (hNl.append (hNh.append (noscope_def _ _))), fun n cfg env cx fr hrel => ?_⟩
    rw [hr]
    cases n with
    | zero => simp only [evalExpr]; exact Sim.timeout
    | succ n =>
      simp only [evalExpr, runS_append]
      refine Sim.bind (hsv n cfg env cx fr hrel) fun vw fr1 ⟨hcv, hrel1, hext1⟩ => ?_
      refine Sim.bind (hsl vw.len 0 n cfg env cx fr1 hrel1) fun lo' fr2 ⟨hbl, hrel2, hext2⟩ => ?_
      refine Sim.bind (hsh vw.len vw.len n cfg env cx fr2 hrel2) fun hi' fr3 ⟨hbh, hrel3, hext3⟩ => ?_
      refine Sim.def_leaf (c := _) RVal.val ?_
      simp only [execPure, getView_of (hext3 _ _ (hext2 _ _ hcv)),
        evalBnd_of (BndRel.ext hext3 hbl), evalBnd_of hbh, bind_assoc, pure_bind]
      by_cases hk : 0 ≤ lo' ∧ lo' ≤ hi' ∧ hi' ≤ (vw.len : Int)
      · simp [hk]
      · simp [hk, abortAtOrg, abortAt, M.stop, bind_apply]
        rfl
  | .len v, h => by
    have hv := viewClaim v (by simpa [exprA] using h)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Ev, hEmv, hSv, hNv, hsv⟩ := hv le ls bb hcur
    simp only [lowerExpr, B.bind_run]
    obtain ⟨hr, hEmc⟩ := emitDef_em (.viewLen (lowerView v le ls).1) le hEmv.cur'
    refine ⟨Ev ++ _, hEmv.trans hEmc, hSv.append (straight_def _ (by simp)),
      hNv.append (noscope_def _ _), fun n cfg env cx fr hrel => ?_⟩
    rw [hr]
    cases n with
    | zero => simp only [evalExpr]; exact Sim.timeout
    | succ n =>
      simp only [evalExpr, runS_append]
      refine Sim.bind (hsv n cfg env cx fr hrel) fun vw fr1 ⟨hc, hrel1, hext1⟩ => ?_
      exact Sim.def_leaf RVal.val (by simp only [execPure, getView_of hc, bind_assoc, pure_bind])
  | .un op a org, h => by
    have ha := exprClaim a (by simpa [exprA] using h)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Ea, hEma, hSa, hNa, hsa⟩ := ha le ls bb hcur
    simp only [lowerExpr, B.bind_run]
    rw [intTyOf_state]
    obtain ⟨hr, hEmc⟩ := emitDef_em (.un op (intTyOf (lowerExpr a le ls).1 le (lowerExpr a le ls).2).1
      (lowerExpr a le ls).1 (some org)) le hEma.cur'
    refine ⟨Ea ++ _, hEma.trans hEmc, hSa.append (straight_def _ (by simp)),
      hNa.append (noscope_def _ _), fun n cfg env cx fr hrel => ?_⟩
    rw [hr]
    cases n with
    | zero => simp only [evalExpr]; exact Sim.timeout
    | succ n =>
      simp only [evalExpr, runS_append]
      refine Sim.bind (hsa n cfg env cx fr hrel) fun va fr1 ⟨hca, hrel1, hext1⟩ => ?_
      refine Sim.expectInt fun t x hva => ?_
      subst hva
      exact Sim.def_leaf RVal.val (execPure_un hrel1.prof hca)
  | .cmp op a b, h => by
    have ha := exprClaim a (by simp [exprA] at h; exact h.1)
    have hb := exprClaim b (by simp [exprA] at h; exact h.2)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Ea, hEma, hSa, hNa, hsa⟩ := ha le ls bb hcur
    obtain ⟨Eb, hEmb, hSb, hNb, hsb⟩ := hb le (lowerExpr a le ls).2 bb hEma.cur'
    simp only [lowerExpr, B.bind_run, valTy_state]
    generalize (valTy (lowerExpr a le ls).1 le (lowerExpr b le (lowerExpr a le ls).2).2).1 = vt
    have key : ∀ op', (op' = .cmp op (match vt with | .data (.int t) => t | _ => .i64)
          (lowerExpr a le ls).1 (lowerExpr b le (lowerExpr a le ls).2).1 ∨
        op' = .boolCmp op (lowerExpr a le ls).1 (lowerExpr b le (lowerExpr a le ls).2).1) →
        ∃ E, Em bb ls (emitDef op' le (lowerExpr b le (lowerExpr a le ls).2).2).2 E ∧ Straight E ∧ NoScope E ∧
          ∀ n cfg env cx fr, Rel cfg env cx fr ls →
            Sim (evalExpr n cfg env (.cmp op a b)) (runS cx fr E)
              (fun v fr' => fr'.vals[(emitDef op' le (lowerExpr b le (lowerExpr a le ls).2).2).1]? = some (.val v)) := by
      intro op' hop'
      have hnc : ∀ f a o, op' ≠ .call f a o := by
        intro f a' o h'; rcases hop' with h1 | h1 <;> (subst h1; cases h')
      obtain ⟨hr, hEmc⟩ := emitDef_em op' le hEmb.cur'
      refine ⟨Ea ++ (Eb ++ _), hEma.trans (hEmb.trans hEmc), hSa.append (hSb.append (straight_def _ hnc)),
        hNa.append (hNb.append (noscope_def _ _)), fun n cfg env cx fr hrel => ?_⟩
      rw [hr]
      cases n with
      | zero => simp only [evalExpr]; exact Sim.timeout
      | succ n =>
        simp only [evalExpr, runS_append]
        refine Sim.bind (hsa n cfg env cx fr hrel) fun va fr1 ⟨hca, hrel1, hext1⟩ => ?_
        refine Sim.bind (hsb n cfg env cx fr1 hrel1) fun vb fr2 ⟨hcb, hrel2, hext2⟩ => ?_
        have hc1 := hext2 _ _ hca
        rcases hop' with h1 | h1 <;> subst h1
        · exact Sim.def_leaf RVal.val (by
            rw [(execPure_cmp hc1 hcb).1 _])
        · exact Sim.def_leaf RVal.val (by
            rw [(execPure_cmp hc1 hcb).2])
    cases vt with
    | data t =>
      cases t with
      | int t => exact key _ (Or.inl rfl)
      | _ => exact key _ (Or.inr rfl)
    | view _ _ => exact key _ (Or.inr rfl)
  | .not a, h => by
    have ha := exprClaim a (by simpa [exprA] using h)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Ea, hEma, hSa, hNa, hsa⟩ := ha le ls bb hcur
    simp only [lowerExpr, B.bind_run]
    obtain ⟨hr, hEmc⟩ := emitDef_em (.boolNot (lowerExpr a le ls).1) le hEma.cur'
    refine ⟨Ea ++ _, hEma.trans hEmc, hSa.append (straight_def _ (by simp)),
      hNa.append (noscope_def _ _), fun n cfg env cx fr hrel => ?_⟩
    rw [hr]
    cases n with
    | zero => simp only [evalExpr]; exact Sim.timeout
    | succ n =>
      simp only [evalExpr, runS_append]
      refine Sim.bind (hsa n cfg env cx fr hrel) fun va fr1 ⟨hca, hrel1, hext1⟩ => ?_
      refine Sim.expectBool fun bv hva => ?_
      subst hva
      exact Sim.def_leaf RVal.val (by simp only [execPure, getVal_of hca, Goose.Core.expectBool, bind_assoc, pure_bind])
  | .conv k target a org, h => by
    have ha := exprClaim a (by simpa [exprA] using h)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Ea, hEma, hSa, hNa, hsa⟩ := ha le ls bb hcur
    rw [lowerExpr_conv]
    simp only [B.bind_run]
    rw [intTyOf_state]
    obtain ⟨hr, hEmc⟩ := emitDef_em (.conv k (intTyOf (lowerExpr a le ls).1 le (lowerExpr a le ls).2).1
      (convDst target (intTyOf (lowerExpr a le ls).1 le (lowerExpr a le ls).2).1)
      (lowerExpr a le ls).1 (some org)) le hEma.cur'
    refine ⟨Ea ++ _, hEma.trans hEmc, hSa.append (straight_def _ (by simp)),
      hNa.append (noscope_def _ _), fun n cfg env cx fr hrel => ?_⟩
    rw [hr]
    cases n with
    | zero => simp only [evalExpr]; exact Sim.timeout
    | succ n =>
      simp only [evalExpr, runS_append]
      refine Sim.bind (hsa n cfg env cx fr hrel) fun va fr1 ⟨hca, hrel1, hext1⟩ => ?_
      refine Sim.expectInt fun src x hva => ?_
      subst hva
      refine Sim.expectIntTy fun d htd => ?_
      subst htd
      exact Sim.def_leaf RVal.val (execPure_conv hrel1.prof hca)
  | .push p e, h => by
    have hp := placeClaim p (by simp [exprA] at h; exact h.1)
    have he := exprClaim e (by simp [exprA] at h; exact h.2)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Ep, hEmp, hSp, hNp, hsp⟩ := hp le ls bb hcur
    obtain ⟨Ee, hEme, hSe, hNe, hse⟩ := he le (lowerPlace p le ls).2 bb hEmp.cur'
    simp only [lowerExpr, B.bind_run]
    obtain ⟨hr, hEmc⟩ := emitDef_em (.push (lowerPlace p le ls).1
      (lowerExpr e le (lowerPlace p le ls).2).1 none) le hEme.cur'
    refine ⟨Ep ++ (Ee ++ _), hEmp.trans (hEme.trans hEmc),
      hSp.append (hSe.append (straight_def _ (by simp))),
      hNp.append (hNe.append (noscope_def _ _)), fun n cfg env cx fr hrel => ?_⟩
    rw [hr]
    cases n with
    | zero => simp only [evalExpr]; exact Sim.timeout
    | succ n =>
      simp only [evalExpr, runS_append]
      refine Sim.bind (hsp n cfg env cx fr hrel) fun l fr1 ⟨hcp, hrel1, hext1⟩ => ?_
      refine Sim.bind (hse n cfg env cx fr1 hrel1) fun v fr2 ⟨hce, hrel2, hext2⟩ => ?_
      exact Sim.def_leaf RVal.val (by
        simp only [execPure, getVal_of (hext2 _ _ hcp), getVal_of hce, Goose.Core.expectRef,
          bind_assoc, pure_bind])
  | .arrLit t es, h => by
    have hes := exprsClaim es (by simpa [exprA] using h)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Es, hEms, hSs, hNs, hss⟩ := hes le ls bb hcur
    simp only [lowerExpr, B.bind_run]
    obtain ⟨hr, hEmc⟩ := emitDef_em (.arrLit t (lowerExprs es le ls).1) le hEms.cur'
    refine ⟨Es ++ _, hEms.trans hEmc, hSs.append (straight_def _ (by simp)),
      hNs.append (noscope_def _ _), fun n cfg env cx fr hrel => ?_⟩
    rw [hr]
    cases n with
    | zero => simp only [evalExpr]; exact Sim.timeout
    | succ n =>
      simp only [evalExpr, runS_append]
      refine Sim.bind (hss n cfg env cx fr hrel) fun vs fr1 ⟨hc, hrel1, hext1⟩ => ?_
      exact Sim.def_leaf RVal.val (by
        simp only [execPure, mapList_getVal_of hc, bind_assoc, pure_bind])
  | .fill t e, h => by
    have he := exprClaim e (by simpa [exprA] using h)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Ee, hEme, hSe, hNe, hse⟩ := he le ls bb hcur
    simp only [lowerExpr, B.bind_run]
    obtain ⟨hr, hEmc⟩ := emitDef_em (.arrFill t (lowerExpr e le ls).1) le hEme.cur'
    refine ⟨Ee ++ _, hEme.trans hEmc, hSe.append (straight_def _ (by simp)),
      hNe.append (noscope_def _ _), fun n cfg env cx fr hrel => ?_⟩
    rw [hr]
    cases n with
    | zero => simp only [evalExpr]; exact Sim.timeout
    | succ n =>
      simp only [evalExpr]
      refine Sim.expectFixedCount fun el k htk => ?_
      simp only [runS_append]
      refine Sim.bind (hse n cfg env cx fr hrel) fun v fr1 ⟨hc, hrel1, hext1⟩ => ?_
      subst htk
      exact Sim.def_leaf RVal.val (by
        simp only [execPure, getVal_of hc, Goose.Core.expectFixedCount, bind_assoc, pure_bind])
  | .and .., h => absurd h (by simp [exprA])
  | .or .., h => absurd h (by simp [exprA])
  | .call .., h => absurd h (by simp [exprA])
  | .ifE .., h => absurd h (by simp [exprA])
  | .blockE _, h => absurd h (by simp [exprA])

end

/-! ### Statements -/

theorem Sim.render {v : Val} {f : String → M α} {g : M Frame} {p : α → Frame → Prop}
    (h : ∀ str, (∀ s, Goose.Core.render v s = .ok str s) → Sim (f str) g p) :
    Sim (Goose.Core.render v >>= f) g p := by
  cases v with
  | int t n => exact h (toString n) fun s => rfl
  | bool b => cases b <;> exact h _ fun s => rfl
  | _ =>
    intro s
    refine ⟨fun a s1 hc => ?_, fun e s1 hc hf => ?_⟩
    · simp [Goose.Core.render, fault, M.stop, bind_apply] at hc
    · simp [Goose.Core.render, fault, M.stop, bind_apply] at hc
      obtain ⟨rfl, _⟩ := hc
      exact absurd hf (by simp [IsFinal])

/-- An effect that does what `c0` does and leaves the frame alone, then a Core result. -/
theorem Sim.eff_flow {cx : FnCtx} {fr : Frame} {e : Effect} {c : M β} {c0 : M α} (a0 : β)
    (hc : c = c0 >>= fun _ => pure a0)
    (hx : execEff cx.fn fr e = c0 >>= fun _ => pure fr) :
    Sim c (runS cx fr [.eff e]) (fun a fr' => a = a0 ∧ fr' = fr) := by
  subst hc
  intro s
  have key : ∀ s', runS cx fr [.eff e] s' =
      (match c0 s' with
       | .ok _ s1 => .ok fr s1
       | .stop e s1 => .stop e s1) := by
    intro s'
    simp only [runS, bind_apply, hx]
    cases c0 s' with
    | stop e s1 => rfl
    | ok a s1 => rfl
  refine ⟨fun a s1 hc => ?_, fun e s1 hc _ => ?_⟩
  · rw [bind_apply] at hc
    cases hc0 : c0 s with
    | stop e s2 => rw [hc0] at hc; cases hc
    | ok x s2 =>
      rw [hc0] at hc
      dsimp only at hc
      rw [pure_apply] at hc
      cases hc
      exact ⟨fr, by rw [key s, hc0], rfl, rfl⟩
  · rw [bind_apply] at hc
    cases hc0 : c0 s with
    | stop e2 s2 =>
      rw [hc0] at hc
      cases hc
      rw [key s, hc0]
    | ok x s2 => rw [hc0] at hc; dsimp only at hc; rw [pure_apply] at hc; cases hc

def stmtA : Stmt → Bool
  | .letS _ e _ => exprA e
  | .assign p e _ => placeA p && exprA e
  | .assignOp _ p e _ => placeA p && exprA e
  | .rebind _ e _ => exprA e
  | .expr e _ => exprA e
  | .append p v _ => placeA p && viewA v
  | .print args _ => printA args
  | _ => false
where
  printA : List PrintArg → Bool
    | [] => true
    | .text _ :: rest => printA rest
    | .expr e :: rest => exprA e && printA rest

def PartsRel (fr : Frame) : List PrintPart → List String → Prop
  | [], [] => True
  | .text s :: ps, str :: strs => str = s ∧ PartsRel fr ps strs
  | .val i :: ps, str :: strs =>
    (∃ v, fr.vals[i]? = some (.val v) ∧ ∀ s, Goose.Core.render v s = .ok str s) ∧ PartsRel fr ps strs
  | _, _ => False

theorem PartsRel.ext {fr fr' : Frame} (h : Ext fr fr') :
    ∀ {ps : List PrintPart} {strs : List String}, PartsRel fr ps strs → PartsRel fr' ps strs
  | [], [], _ => trivial
  | .text s :: ps, str :: strs, ⟨h1, h2⟩ => ⟨h1, PartsRel.ext h h2⟩
  | .val i :: ps, str :: strs, ⟨⟨v, hv, hr⟩, h2⟩ => ⟨⟨v, h _ _ hv, hr⟩, PartsRel.ext h h2⟩
  | [], _ :: _, hc => absurd hc (by simp [PartsRel])
  | _ :: _, [], hc => absurd hc (by simp [PartsRel])

theorem mapList_renderPart_of {fr : Frame} :
    ∀ {ps : List PrintPart} {strs : List String}, PartsRel fr ps strs →
      mapList (renderPart fr) ps = pure strs
  | [], [], _ => rfl
  | .text s :: ps, str :: strs, ⟨h1, h2⟩ => by
    subst h1
    simp only [mapList, renderPart, pure_bind, mapList_renderPart_of h2]
  | .val i :: ps, str :: strs, ⟨⟨v, hv, hr⟩, h2⟩ => by
    have : renderPart fr (.val i) = pure str := by
      funext s
      simp only [renderPart, getVal_of hv, pure_bind]
      exact hr s
    simp only [mapList, this, pure_bind, mapList_renderPart_of h2]
  | [], _ :: _, hc => absurd hc (by simp [PartsRel])
  | _ :: _, [], hc => absurd hc (by simp [PartsRel])

mutual
theorem printClaim : ∀ (args : List PrintArg), stmtA.printA args = true →
    Claim (lowerPrintArgs args) (fun n cfg env => mapList (execPrintArg n cfg env) args)
      (fun parts strs fr => PartsRel fr parts strs)
  | [], _ => by
    apply Claim.intro
    intro le ls bb hcur
    simp only [lowerPrintArgs, B.pure_run]
    refine ⟨[], by simpa using Em.refl hcur, by simp [Straight], by simp [NoScope],
      fun n cfg env cx fr hrel => ?_⟩
    simp only [mapList]
    exact Sim.pure' rfl trivial
  | .text str :: rest, h => by
    have hr := printClaim rest (by simpa [stmtA.printA] using h)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Er, hEmr, hSr, hNr, hsr⟩ := hr le ls bb hcur
    simp only [lowerPrintArgs, B.bind_run, B.pure_run]
    refine ⟨Er, hEmr, hSr, hNr, fun n cfg env cx fr hrel => ?_⟩
    cases n with
    | zero =>
      simp only [mapList, execPrintArg, pure_bind]
      exact Sim.timeout
    | succ n =>
      simp only [mapList, execPrintArg, pure_bind]
      refine Sim.of_bind_pure (Sim.bind (hsr (n + 1) cfg env cx fr hrel) fun strs fr1 ⟨hc, _, _⟩ => ?_)
      exact Sim.pure' rfl ⟨rfl, hc⟩
  | .expr e :: rest, h => by
    have he := exprClaim e (by simp [stmtA.printA] at h; exact h.1)
    have hr := printClaim rest (by simp [stmtA.printA] at h; exact h.2)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Ee, hEme, hSe, hNe, hse⟩ := he le ls bb hcur
    obtain ⟨Er, hEmr, hSr, hNr, hsr⟩ := hr le (lowerExpr e le ls).2 bb hEme.cur'
    simp only [lowerPrintArgs, B.bind_run, B.pure_run]
    refine ⟨Ee ++ Er, hEme.trans hEmr, hSe.append hSr, hNe.append hNr, fun n cfg env cx fr hrel => ?_⟩
    cases n with
    | zero =>
      simp only [mapList, execPrintArg, bind_assoc]
      exact Sim.timeout
    | succ n =>
      simp only [mapList, execPrintArg, bind_assoc, runS_append]
      refine Sim.bind (hse n cfg env cx fr hrel) fun v fr1 ⟨hc, hrel1, hext1⟩ => ?_
      refine Sim.render fun str hstr => ?_
      refine Sim.of_bind_pure (Sim.bind (hsr (n + 1) cfg env cx fr1 hrel1) fun strs fr2 ⟨hcs, _, hext2⟩ => ?_)
      exact Sim.pure' rfl ⟨⟨v, hext2 _ _ hc, hstr⟩, hcs⟩
end

theorem Sim.congr_core {c c' : M α} {g : M Frame} {p : α → Frame → Prop} (h : c = c')
    (hs : Sim c' g p) : Sim c g p := by
  subst h; exact hs

theorem Sim.def_leaf_rel {cfg : Cfg} {env : Env} {cx : FnCtx} {fr : Frame} {ls ls' : LS}
    {b : BlockId} {r : ValueId} {op : Op} {c : M α} (inj : α → RVal)
    (hrel : Rel cfg env cx fr ls) (hem : Em b ls ls' [.def r op])
    (hx : execPure cx fr op = c >>= fun a => pure (inj a)) :
    Sim c (runS cx fr [.def r op]) (fun a fr' =>
      fr'.vals[r]? = some (inj a) ∧ Rel cfg env cx fr' ls' ∧ Ext fr fr') :=
  (Sim.def_leaf inj hx).strengthen (Q := fun fr' => Rel cfg env cx fr' ls' ∧ Ext fr fr')
    (fun s fr' s1 hr => rel_after hrel hem (noscope_def _ _) hr)

theorem Sim.eff_flow_rel {cfg : Cfg} {env : Env} {cx : FnCtx} {fr : Frame} {ls ls' : LS}
    {b : BlockId} {e : Effect} {c : M β} {c0 : M α} (a0 : β) (he : EffPlain e)
    (hrel : Rel cfg env cx fr ls) (hem : Em b ls ls' [.eff e])
    (hc : c = c0 >>= fun _ => pure a0)
    (hx : execEff cx.fn fr e = c0 >>= fun _ => pure fr) :
    Sim c (runS cx fr [.eff e]) (fun a fr' => (a = a0 ∧ fr' = fr) ∧ Rel cfg env cx fr' ls' ∧ Ext fr fr') :=
  (Sim.eff_flow a0 hc hx).strengthen (Q := fun fr' => Rel cfg env cx fr' ls' ∧ Ext fr fr')
    (fun s fr' s1 hr => rel_after hrel hem (noscope_eff he) hr)

theorem stmtClaim (lc : Option LoopCtx) : ∀ (s : Stmt), stmtA s = true →
    Claim (lowerStmt lc s) (fun n cfg env => execStmt n cfg env s)
      (fun _ f _ => f = Flow.normal .unit)
  | .letS x e org, h => by
    have he := exprClaim e (by simpa [stmtA] using h)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Ee, hEme, hSe, hNe, hse⟩ := he le ls bb hcur
    simp only [lowerStmt, B.bind_run]
    have hem := emitEffect_em (.slotInit x (lowerExpr e le ls).1 (some org)) le hEme.cur'
    refine ⟨Ee ++ _, hEme.trans hem, hSe.append (straight_eff _),
      hNe.append (noscope_eff trivial), fun n cfg env cx fr hrel => ?_⟩
    cases n with
    | zero => simp only [execStmt]; exact Sim.timeout
    | succ n =>
      simp only [execStmt, runS_append]
      refine Sim.bind (hse n cfg env cx fr hrel) fun v fr1 ⟨hc, hrel1, hext1⟩ => ?_
      refine Sim.mono (Sim.eff_flow (c0 := rootOf env x >>= fun r => bindRoot r v)
        (Flow.normal .unit) (by simp only [bind_assoc]) ?_) (fun a fr' h => h.1)
      simp only [execEff, slotRoot_eq hrel1, getVal_of hc, bind_assoc, pure_bind]
  | .assign p e org, h => by
    have hp := placeClaim p (by simp [stmtA] at h; exact h.1)
    have he := exprClaim e (by simp [stmtA] at h; exact h.2)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Ep, hEmp, hSp, hNp, hsp⟩ := hp le ls bb hcur
    obtain ⟨Ee, hEme, hSe, hNe, hse⟩ := he le (lowerPlace p le ls).2 bb hEmp.cur'
    simp only [lowerStmt, B.bind_run]
    have hem := emitEffect_em (.store (lowerPlace p le ls).1
      (lowerExpr e le (lowerPlace p le ls).2).1 (some org)) le hEme.cur'
    refine ⟨Ep ++ (Ee ++ _), hEmp.trans (hEme.trans hem), hSp.append (hSe.append (straight_eff _)),
      hNp.append (hNe.append (noscope_eff trivial)), fun n cfg env cx fr hrel => ?_⟩
    cases n with
    | zero => simp only [execStmt]; exact Sim.timeout
    | succ n =>
      simp only [execStmt, runS_append]
      refine Sim.bind (hsp n cfg env cx fr hrel) fun l fr1 ⟨hcp, hrel1, hext1⟩ => ?_
      refine Sim.bind (hse n cfg env cx fr1 hrel1) fun v fr2 ⟨hce, hrel2, hext2⟩ => ?_
      refine Sim.mono (Sim.eff_flow (c0 := writeLoc l v) (Flow.normal .unit) rfl ?_) (fun a fr' h => h.1)
      simp only [execEff, getVal_of (hext2 _ _ hcp), getVal_of hce, Goose.Core.expectRef, bind_assoc, pure_bind]
  | .rebind x e org, h => by
    have he := exprClaim e (by simpa [stmtA] using h)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Ee, hEme, hSe, hNe, hse⟩ := he le ls bb hcur
    simp only [lowerStmt, B.bind_run]
    obtain ⟨hr, hEmr⟩ := emitDef_em (.slotAddr x) le hEme.cur'
    have hem := emitEffect_em (.store (emitDef (.slotAddr x) le (lowerExpr e le ls).2).1
      (lowerExpr e le ls).1 (some org)) le hEmr.cur'
    refine ⟨Ee ++ ([.def _ (.slotAddr x)] ++ [.eff (.store (emitDef (.slotAddr x) le (lowerExpr e le ls).2).1
      (lowerExpr e le ls).1 (some org))]), hEme.trans (hEmr.trans hem),
      hSe.append ((straight_def _ (by simp)).append (straight_eff _)),
      hNe.append ((noscope_def _ _).append (noscope_eff (e := .store _ _ _) trivial)), fun n cfg env cx fr hrel => ?_⟩
    cases n with
    | zero => simp only [execStmt, bind_assoc]; exact Sim.timeout
    | succ n =>
      simp only [execStmt, runS_append, bind_assoc]
      refine Sim.bind (hse n cfg env cx fr hrel) fun v fr1 ⟨hc, hrel1, hext1⟩ => ?_
      rw [show (rootOf env x >>= fun r => writeLoc ⟨r, []⟩ v >>= fun _ => pure (Flow.normal .unit)) =
        ((rootOf env x >>= fun r => pure (Loc.mk r [])) >>= fun l => writeLoc l v >>= fun _ => pure (Flow.normal .unit))
        by simp [bind_assoc]]
      refine Sim.bind (Sim.def_leaf_rel (c := rootOf env x >>= fun r => pure (Loc.mk r []))
        (fun l => RVal.val (.ref l)) hrel1 hEmr
        (by simp only [execPure, slotRoot_eq hrel1, bind_assoc, pure_bind])) fun l fr2 ⟨hl, hrel2, hext2⟩ => ?_
      refine Sim.mono (Sim.eff_flow_rel (c0 := writeLoc l v) (Flow.normal .unit) trivial hrel2 hem rfl ?_)
        (fun a fr' h => h.1.1)
      simp only [execEff, hr, getVal_of hl, getVal_of (hext2 _ _ hc), Goose.Core.expectRef, bind_assoc, pure_bind]
  | .expr e _, h => by
    have he := exprClaim e (by simpa [stmtA] using h)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Ee, hEme, hSe, hNe, hse⟩ := he le ls bb hcur
    simp only [lowerStmt, B.bind_run, B.pure_run]
    refine ⟨Ee, hEme, hSe, hNe, fun n cfg env cx fr hrel => ?_⟩
    cases n with
    | zero => simp only [execStmt]; exact Sim.timeout
    | succ n =>
      simp only [execStmt]
      refine Sim.of_bind_pure (Sim.bind (hse n cfg env cx fr hrel) fun v fr1 ⟨hc, _, _⟩ => ?_)
      exact Sim.pure' rfl rfl
  | .append owner src org, h => by
    have hp := placeClaim owner (by simp [stmtA] at h; exact h.1)
    have hv := viewClaim src (by simp [stmtA] at h; exact h.2)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Ep, hEmp, hSp, hNp, hsp⟩ := hp le ls bb hcur
    obtain ⟨Ev, hEmv, hSv, hNv, hsv⟩ := hv le (lowerPlace owner le ls).2 bb hEmp.cur'
    simp only [lowerStmt, B.bind_run]
    have hem := emitEffect_em (.append (lowerPlace owner le ls).1
      (lowerView src le (lowerPlace owner le ls).2).1 (some org)) le hEmv.cur'
    refine ⟨Ep ++ (Ev ++ _), hEmp.trans (hEmv.trans hem), hSp.append (hSv.append (straight_eff _)),
      hNp.append (hNv.append (noscope_eff trivial)), fun n cfg env cx fr hrel => ?_⟩
    cases n with
    | zero => simp only [execStmt]; exact Sim.timeout
    | succ n =>
      simp only [execStmt, runS_append]
      refine Sim.bind (hsp n cfg env cx fr hrel) fun l fr1 ⟨hcp, hrel1, hext1⟩ => ?_
      refine Sim.bind (hsv n cfg env cx fr1 hrel1) fun vw fr2 ⟨hcv, hrel2, hext2⟩ => ?_
      refine Sim.mono (Sim.eff_flow (c0 := readRun vw >>= fun elems => appendLoc l elems)
        (Flow.normal .unit) (by simp only [bind_assoc]) ?_) (fun a fr' h => h.1)
      simp only [execEff, getVal_of (hext2 _ _ hcp), getView_of hcv, Goose.Core.expectRef, bind_assoc, pure_bind]
  | .print args org, h => by
    have hr := printClaim args (by simpa [stmtA] using h)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Er, hEmr, hSr, hNr, hsr⟩ := hr le ls bb hcur
    simp only [lowerStmt, B.bind_run]
    have hem := emitEffect_em (.print (lowerPrintArgs args le ls).1 (some org)) le hEmr.cur'
    refine ⟨Er ++ _, hEmr.trans hem, hSr.append (straight_eff _),
      hNr.append (noscope_eff trivial), fun n cfg env cx fr hrel => ?_⟩
    cases n with
    | zero => simp only [execStmt]; exact Sim.timeout
    | succ n =>
      simp only [execStmt, runS_append]
      refine Sim.bind (hsr n cfg env cx fr hrel) fun strs fr1 ⟨hc, hrel1, hext1⟩ => ?_
      refine Sim.mono (Sim.eff_flow (c0 := emit (String.join strs ++ "\n"))
        (Flow.normal .unit) (by simp only [bind_assoc]) ?_) (fun a fr' h => h.1)
      simp only [execEff, mapList_renderPart_of hc, bind_assoc, pure_bind]
  | .assignOp op p e org, h => by
    have hp := placeClaim p (by simp [stmtA] at h; exact h.1)
    have he := exprClaim e (by simp [stmtA] at h; exact h.2)
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Ep, hEmp, hSp, hNp, hsp⟩ := hp le ls bb hcur
    rcases hpl : lowerPlace p le ls with ⟨r, ls1⟩
    simp only [hpl] at hEmp hsp
    obtain ⟨hr1, hEml⟩ := emitDef_em (.load r) le hEmp.cur'
    rcases hl : emitDef (.load r) le ls1 with ⟨old, ls2⟩
    simp only [hl] at hr1 hEml
    subst hr1
    obtain ⟨Ee, hEme, hSe, hNe, hse⟩ := he le ls2 bb hEml.cur'
    rcases hel : lowerExpr e le ls2 with ⟨rhs, ls3⟩
    simp only [hel] at hEme hse
    have hty := intTyOf_state ls1.vals.size le ls3
    simp only [lowerStmt, B.bind_run, hpl, hl, hel]
    rw [hty]
    generalize (intTyOf ls1.vals.size le ls3).1 = ty
    obtain ⟨hr2, hEmb⟩ := emitDef_em (.bin op ty ls1.vals.size rhs (some org)) le hEme.cur'
    rcases hb : emitDef (.bin op ty ls1.vals.size rhs (some org)) le ls3 with ⟨res, ls4⟩
    simp only [hb] at hr2 hEmb ⊢
    subst hr2
    have hem := emitEffect_em (.store r ls3.vals.size (some org)) le hEmb.cur'
    refine ⟨Ep ++ ([.def _ (.load r)] ++ (Ee ++ ([.def _ (.bin op ty ls1.vals.size rhs (some org))] ++ [.eff (.store r ls3.vals.size (some org))]))),
      hEmp.trans (hEml.trans (hEme.trans (hEmb.trans hem))),
      hSp.append ((straight_def _ (by simp)).append (hSe.append ((straight_def _ (by simp)).append (straight_eff _)))),
      hNp.append ((noscope_def _ _).append (hNe.append ((noscope_def _ _).append (noscope_eff (e := .store _ _ _) trivial)))),
      fun n cfg env cx fr hrel => ?_⟩
    cases n with
    | zero => simp only [execStmt]; exact Sim.timeout
    | succ n =>
      simp only [execStmt, runS_append]
      refine Sim.bind (hsp n cfg env cx fr hrel) fun l fr1 ⟨hcp, hrel1, hext1⟩ => ?_
      refine Sim.bind (Sim.def_leaf_rel (c := readLoc l) RVal.val hrel1 hEml
        (by simp only [execPure, getVal_of hcp, Goose.Core.expectRef, bind_assoc, pure_bind]))
        fun ov fr2 ⟨hold, hrel2, hext2⟩ => ?_
      refine Sim.expectInt fun t x hov => ?_
      subst hov
      refine Sim.bind (hse n cfg env cx fr2 hrel2) fun ev fr3 ⟨hce, hrel3, hext3⟩ => ?_
      refine Sim.expectInt fun u y hev => ?_
      subst hev
      refine Sim.expectSameTy fun htu => ?_
      subst htu
      dsimp only
      refine Sim.congr_core (c' := (match evalBin cfg.profile op t x y with
            | .ok r => pure (Val.int t r)
            | .error k => abortAt (AbortKind.ofNum k) org) >>= fun v =>
            writeLoc l v >>= fun _ => pure (Flow.normal .unit))
        (by cases evalBin cfg.profile op t x y <;> rfl) ?_
      refine Sim.bind (Sim.def_leaf_rel (c := _) RVal.val hrel3 hEmb
        (execPure_bin hrel3.prof (hext3 _ _ hold) hce)) fun v fr4 ⟨hres, hrel4, hext4⟩ => ?_
      refine Sim.mono (Sim.eff_flow_rel (c0 := writeLoc l v) (Flow.normal .unit) trivial hrel4 hem rfl ?_)
        (fun a fr' h => h.1.1)
      simp only [execEff, getVal_of (hext4 _ _ (hext3 _ _ (hext2 _ _ hcp))), getVal_of hres,
        Goose.Core.expectRef, bind_assoc, pure_bind]
  | .ifS .., h => absurd h (by simp [stmtA])
  | .while .., h => absurd h (by simp [stmtA])
  | .forRange .., h => absurd h (by simp [stmtA])
  | .forEach .., h => absurd h (by simp [stmtA])
  | .ret .., h => absurd h (by simp [stmtA])
  | .brk _, h => absurd h (by simp [stmtA])
  | .cont _, h => absurd h (by simp [stmtA])
  | .assertS .., h => absurd h (by simp [stmtA])
  | .abort .., h => absurd h (by simp [stmtA])
  | .exit .., h => absurd h (by simp [stmtA])

theorem isLive_run {ls : LS} {b : BlockId} (h : ls.cur = some b) (le : LEnv) :
    isLive le ls = (true, ls) := by
  simp [isLive, curBlock, bind, get, pure, h]

theorem stmtsClaim (lc : Option LoopCtx) : ∀ (ss : List Stmt), (∀ s ∈ ss, stmtA s = true) →
    Claim (lowerStmts lc ss) (fun n cfg env => execStmts n cfg env ss)
      (fun _ f _ => f = Flow.normal .unit)
  | [], _ => by
    apply Claim.intro
    intro le ls bb hcur
    simp only [lowerStmts, B.pure_run]
    refine ⟨[], by simpa using Em.refl hcur, by simp [Straight], by simp [NoScope],
      fun n cfg env cx fr hrel => ?_⟩
    cases n with
    | zero => simp only [execStmts]; exact Sim.timeout
    | succ n =>
      simp only [execStmts]
      exact Sim.pure' rfl rfl
  | s :: rest, h => by
    have hs := stmtClaim lc s (h s (by simp))
    have hr := stmtsClaim lc rest (fun t ht => h t (by simp [ht]))
    apply Claim.intro
    intro le ls bb hcur
    obtain ⟨Es, hEms, hSs, hNs, hss⟩ := hs le ls bb hcur
    obtain ⟨Er, hEmr, hSr, hNr, hsr⟩ := hr le (lowerStmt lc s le ls).2 bb hEms.cur'
    simp only [lowerStmts, B.bind_run, isLive_run hcur]
    simp only [ite_true, B.bind_run]
    refine ⟨Es ++ Er, hEms.trans hEmr, hSs.append hSr, hNs.append hNr, fun n cfg env cx fr hrel => ?_⟩
    cases n with
    | zero => simp only [execStmts]; exact Sim.timeout
    | succ n =>
      simp only [execStmts, runS_append]
      refine Sim.bind (hss n cfg env cx fr hrel) fun f fr1 ⟨hf, hrel1, hext1⟩ => ?_
      subst hf
      exact (hsr n cfg env cx fr1 hrel1).mono fun a fr' h => h.1

/-! ### Scopes and blocks -/

theorem releaseSlots_eq {fn : Func} {vars : Array LocalVar}
    (hs : fn.slots = vars.mapIdx fun i lv => (⟨lv.ty, lv.kind, lv.scope, i⟩ : Slot))
    (act : ActId) (sc : Nat) (si : ScopeInst) :
    ∀ (n : Nat) (st : Store), releaseSlots fn act sc si n st = releaseVars vars act sc si n st
  | 0, st => rfl
  | n + 1, st => by
    simp only [releaseSlots, releaseVars, hs, Array.getElem?_mapIdx]
    cases vars[n]? with
    | none => exact releaseSlots_eq hs act sc si n st
    | some lv => simpa using releaseSlots_eq hs act sc si n _

theorem releaseScope_eq {cfg : Cfg} {env : Env} {cx : FnCtx} {fr : Frame} {ls : LS}
    (hrel : Rel cfg env cx fr ls) (sc : Nat) (si : ScopeInst) :
    GIR.releaseScope cx.fn fr.act sc si = Core.releaseScope env sc si := by
  funext s
  have hsz : cx.fn.slots.size = env.vars.size := by rw [hrel.slots]; simp
  simp only [GIR.releaseScope, Core.releaseScope, hrel.act, hsz]
  rw [releaseSlots_eq hrel.slots]

theorem Sim.eff_map {cx : FnCtx} {fr : Frame} {e : Effect} {c : M α} (f : α → Frame)
    (hx : execEff cx.fn fr e = c >>= fun a => pure (f a)) :
    Sim c (runS cx fr [.eff e]) (fun a fr' => fr' = f a) := by
  intro s
  have key : ∀ s', runS cx fr [.eff e] s' =
      (match c s' with
       | .ok a s1 => .ok (f a) s1
       | .stop e s1 => .stop e s1) := by
    intro s'
    simp only [runS, bind_apply, hx]
    cases c s' with
    | stop e s1 => rfl
    | ok a s1 => rfl
  refine ⟨fun a s1 hc => ?_, fun e s1 hc _ => ?_⟩
  · rw [key s, hc]
    exact ⟨_, rfl, rfl⟩
  · rw [key s, hc]

theorem Em.pushScope {b : BlockId} {ls ls' : LS} {E : List Inst} (h : Em b ls ls' E) (sc : ScopeId)
    (le : LEnv) : Em b ls ((Lower.pushScope sc : B Unit) le ls').2 E :=
  ⟨h.cur, h.cur', h.blocks, h.mono, h.fresh⟩

theorem Em.popScope {b : BlockId} {ls ls' : LS} {E : List Inst} (h : Em b ls ls' E)
    (le : LEnv) : Em b ls ((Lower.popScope : B Unit) le ls').2 E :=
  ⟨h.cur, h.cur', h.blocks, h.mono, h.fresh⟩

def blockA : Core.Block → Bool
  | .mk _ ss v => ss.all stmtA && (match v with | none => true | some e => exprA e)

theorem Rel.of_size {cfg : Cfg} {env : Env} {cx : FnCtx} {fr : Frame} {ls ls' : LS}
    (h : Rel cfg env cx fr ls) (hs : ls.vals.size = ls'.vals.size) : Rel cfg env cx fr ls' :=
  ⟨h.prof, h.slots, h.act, h.scopes, h.depth, fun k hk => hs ▸ h.below k hk⟩

/-- Entering a scope. -/
theorem enter_sim {cfg : Cfg} {env : Env} {cx : FnCtx} {fr : Frame} {ls ls1 : LS} {b : BlockId}
    (sc : ScopeId) (hrel : Rel cfg env cx fr ls) (hem : Em b ls ls1 [.eff (.enter sc)]) :
    Sim freshScope (runS cx fr [.eff (.enter sc)]) (fun si fr1 =>
      fr1 = { fr with scopes := (sc, si) :: fr.scopes } ∧
      Rel cfg { env with scopes := (sc, si) :: env.scopes } cx fr1 ls1 ∧ Ext fr fr1) := by
  refine (Sim.eff_map (fun si => { fr with scopes := (sc, si) :: fr.scopes }) rfl).mono ?_
  intro si fr1 h1
  subst h1
  refine ⟨rfl, ⟨hrel.prof, hrel.slots, hrel.act, by simp [hrel.scopes], hrel.depth, fun k hk => ?_⟩,
    fun k x hk => hk⟩
  exact Nat.lt_of_lt_of_le (hrel.below k hk) hem.mono

/-- Leaving the scope that was entered last. -/
theorem leave_sim {cfg : Cfg} {env : Env} {cx : FnCtx} {fr : Frame} {ls ls1 : LS} {b : BlockId}
    (sc : ScopeId) (si : ScopeInst) {β : Type} (x : β)
    (hrel : Rel cfg { env with scopes := (sc, si) :: env.scopes } cx fr ls)
    (hem : Em b ls ls1 [.eff (.leave sc)]) :
    Sim (Core.releaseScope env sc si >>= fun _ => pure x) (runS cx fr [.eff (.leave sc)])
      (fun a fr' => a = x ∧ fr' = { fr with scopes := env.scopes } ∧ Rel cfg env cx fr' ls1 ∧ Ext fr fr') := by
  have hsc : fr.scopes = (sc, si) :: env.scopes := hrel.scopes
  have heq := releaseScope_eq hrel sc si
  have hx : execEff cx.fn fr (.leave sc) =
      Core.releaseScope env sc si >>= fun _ => pure ({ fr with scopes := env.scopes } : Frame) := by
    simp only [execEff, hsc, ↓reduceIte]
    rw [heq]
    rfl
  refine Sim.of_bind_pure ?_
  have h1 := Sim.eff_map (cx := cx) (fr := fr) (e := .leave sc) (c := Core.releaseScope env sc si)
    (fun _ => ({ fr with scopes := env.scopes } : Frame))
    (by simpa using hx)
  refine Sim.bind h1 fun u fr' h => ?_
  subst h
  refine Sim.pure' rfl ⟨rfl, rfl, ⟨hrel.prof, hrel.slots, hrel.act, rfl, hrel.depth, fun k hk => ?_⟩,
    fun k x hk => hk⟩
  exact Nat.lt_of_lt_of_le (hrel.below k hk) hem.mono

theorem Sim.bind_pure_left {c : M α} {g1 : M Frame} {g2 : Frame → M Frame} {fr1 : Frame}
    {p : α → Frame → Prop} (hg : g1 = pure fr1) (h : Sim c (g2 fr1) p) : Sim c (g1 >>= g2) p := by
  subst hg
  simpa using h

theorem runS_constUnit (cx : FnCtx) (fr : Frame) (r : ValueId) :
    runS cx fr [.def r .constUnit] =
      pure ({ fr with vals := fr.vals.insert r (.val .unit) } : Frame) := by
  simp [runS, execPure, setCell]

/-- A straight-line block, entered in a fresh scope. -/
def BlockClaim (want : Bool) (blk : Core.Block) : Prop :=
  ∀ (le : LEnv) (ls : LS) (b : BlockId), ls.cur = some b →
    ∃ E, Em b ls (lowerBlock none [] want blk le ls).2 E ∧ Straight E ∧
      ∀ n cfg env cx fr, Rel cfg env cx fr ls →
        Sim (execBlock n cfg env [] blk) (runS cx fr E)
          (fun f fr' => ∃ v, f = Flow.normal v ∧ (blk.value.isNone → v = .unit) ∧
            ((blk.value.isSome ∨ want = true) →
              fr'.vals[(lowerBlock none [] want blk le ls).1]? = some (.val v)) ∧
            Rel cfg env cx fr' (lowerBlock none [] want blk le ls).2 ∧ Ext fr fr')

theorem blockClaim (want : Bool) : ∀ blk : Core.Block, blockA blk = true → BlockClaim want blk
  | .mk sc stmts value, h => by
    intro le ls bb hcur
    have hall : ∀ s ∈ stmts, stmtA s = true := by
      simp only [blockA, Bool.and_eq_true, List.all_eq_true] at h
      exact h.1
    have hem1 := emitEffect_em (.enter sc) le hcur
    have hem1' := hem1.pushScope sc le
    obtain ⟨Es, hEms, hSs, hNs, hss⟩ := stmtsClaim none stmts hall le _ bb hem1'.cur'
    cases value with
    | some e =>
      have he := exprClaim e (by simp [blockA] at h; exact h.2)
      obtain ⟨Ev, hEmv, hSv, hNv, hsv⟩ := he le _ bb hEms.cur'
      simp only [lowerBlock, B.bind_run, B.pure_run, initSlots]
      have hem3 := emitEffect_em (.leave sc) le hEmv.cur'
      refine ⟨[.eff (.enter sc)] ++ (Es ++ (Ev ++ [.eff (.leave sc)])), ?_,
        (straight_eff _).append (hSs.append (hSv.append (straight_eff _))), ?_⟩
      · have := ((hem1'.trans hEms).trans hEmv).trans hem3
        simpa [List.append_assoc] using this.popScope le
      · intro n cfg env cx fr hrel
        cases n with
        | zero => simp only [execBlock]; exact Sim.timeout
        | succ n =>
          simp only [execBlock, runS_append, bindAll, pure_bind]
          refine Sim.bind (enter_sim sc hrel hem1) fun si fr1 ⟨hfr1, hrel1, hext1⟩ => ?_
          refine Sim.bind (hss n cfg _ cx fr1 (hrel1.of_size rfl)) fun f fr2 ⟨hf, hrel2, hext2⟩ => ?_
          subst hf
          simp only []
          refine Sim.bind (hsv n cfg _ cx fr2 hrel2) fun v fr3 ⟨hc, hrel3, hext3⟩ => ?_
          refine Sim.mono (leave_sim sc si (Flow.normal v) hrel3 hem3) ?_
          intro a fr4 ⟨ha, hfr4, hrel4, hext4⟩
          subst hfr4
          exact ⟨v, ha, fun hh => by simp [Core.Block.value] at hh, fun _ => hc, hrel4.of_size rfl,
            hext1.trans (hext2.trans (hext3.trans hext4))⟩
    | none =>
      simp only [lowerBlock, B.bind_run, B.pure_run, initSlots]
      cases want with
      | true =>
        simp only [ite_true, B.bind_run, B.pure_run]
        obtain ⟨hr2, hEmu⟩ := emitDef_em .constUnit le hEms.cur'
        have hem3 := emitEffect_em (.leave sc) le hEmu.cur'
        generalize hvid : (lowerStmts none stmts le (pushScope sc le (emitEffect (.enter sc) le ls).2).2).2.vals.size = vid at hr2 hEmu hem3
        refine ⟨(([.eff (.enter sc)] ++ Es) ++ [.def vid .constUnit]) ++ [.eff (.leave sc)], ?_,
          (((straight_eff _).append hSs).append (straight_def _ (by simp))).append (straight_eff _), ?_⟩
        · exact (((hem1'.trans hEms).trans hEmu).trans hem3).popScope le
        · intro n cfg env cx fr hrel
          cases n with
          | zero => simp only [execBlock]; exact Sim.timeout
          | succ n =>
            simp only [execBlock, List.append_assoc, runS_append, bindAll, pure_bind]
            refine Sim.bind (enter_sim sc hrel hem1) fun si fr1 ⟨hfr1, hrel1, hext1⟩ => ?_
            refine Sim.bind (hss n cfg _ cx fr1 (hrel1.of_size rfl)) fun f fr2 ⟨hf, hrel2, hext2⟩ => ?_
            subst hf
            refine Sim.bind_pure_left (runS_constUnit cx fr2 _) ?_
            have hrel3 := rel_after (s := St.initial) hrel2 hEmu (noscope_def _ _)
              (by rw [runS_constUnit]; rfl)
            refine Sim.mono (leave_sim sc si (Flow.normal .unit) hrel3.1 hem3) ?_
            intro a fr4 ⟨ha, hfr4, hrel4, hext4⟩
            subst hfr4
            exact ⟨.unit, ha, fun _ => rfl, fun _ => by simpa [hr2] using cell_insert fr2 _ (.val .unit),
              hrel4.of_size rfl, hext1.trans (hext2.trans (hrel3.2.trans hext4))⟩
      | false =>
        simp only [Bool.false_eq_true, ite_false, B.bind_run, B.pure_run]
        have hem3 := emitEffect_em (.leave sc) le hEms.cur'
        refine ⟨([.eff (.enter sc)] ++ Es) ++ [.eff (.leave sc)], ?_,
          ((straight_eff _).append hSs).append (straight_eff _), ?_⟩
        · exact ((hem1'.trans hEms).trans hem3).popScope le
        · intro n cfg env cx fr hrel
          cases n with
          | zero => simp only [execBlock]; exact Sim.timeout
          | succ n =>
            simp only [execBlock, List.append_assoc, runS_append, bindAll, pure_bind]
            refine Sim.bind (enter_sim sc hrel hem1) fun si fr1 ⟨hfr1, hrel1, hext1⟩ => ?_
            refine Sim.bind (hss n cfg _ cx fr1 (hrel1.of_size rfl)) fun f fr2 ⟨hf, hrel2, hext2⟩ => ?_
            subst hf
            refine Sim.mono (leave_sim sc si (Flow.normal .unit) hrel2 hem3) ?_
            intro a fr4 ⟨ha, hfr4, hrel4, hext4⟩
            subst hfr4
            exact ⟨.unit, ha, fun _ => rfl, fun hh => by simp [Core.Block.value] at hh,
              hrel4.of_size rfl, hext1.trans (hext2.trans hext4)⟩

end Goose.Proofs.Lower
