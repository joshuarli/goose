import Goose.Lower.Frag
import Goose.GIR.Step

/-!
The relation between a Core run and the run of the lowered function, and the facts about the
builder that a simulation step reads off the finished function.
-/

namespace Goose.Lower

open Goose.Core
open Goose.GIR (ValueId BlockId SlotId ScopeId FnId VTy Bnd PrintPart Op Effect Term Inst Pt instAt
  instsAt runAt Frame FnCtx RVal Func Slot)
open Goose.GIR

/-! ### Program points of the builder, and the finished function -/

/-- The program point the builder is at: the current block and the number of instructions in it. -/
def LS.pp (ls : LS) : Option Pt :=
  match ls.cur with
  | some b => (ls.blocks[b]?).map fun blk => (b, blk.insts.size)
  | none => none

/-- The instruction at a program point of a block table. -/
def instAtT (T : Array GIR.Block) (pt : Pt) : Option Inst :=
  (T[pt.1]?).bind fun b => b.insts[pt.2]?

theorem instAt_eq (fn : Func) (pt : Pt) : instAt fn pt = instAtT fn.blocks pt := rfl

/-- The block table `T` extends the builder's: each block keeps its parameters and the instructions
emitted so far, and may continue. -/
def ExtT (ls : LS) (T : Array GIR.Block) : Prop :=
  ls.blocks.size ≤ T.size ∧
  ∀ (i : Nat) (blk : BlockB), ls.blocks[i]? = some blk → ∃ blk' : GIR.Block, T[i]? = some blk' ∧
    blk'.params = blk.params ∧ ∃ E, blk'.insts = blk.insts.toList ++ E

theorem ExtT.of_ext {ls ls' : LS} {T : Array GIR.Block} (h : ExtT ls' T) (he : ls.Ext ls') : ExtT ls T := by
  refine ⟨Nat.le_trans he.1 h.1, fun i blk hi => ?_⟩
  obtain ⟨b1, hb1, hp1, E1, he1⟩ := he.2 i blk hi
  obtain ⟨b2, hb2, hp2, E2, he2⟩ := h.2 i b1 hb1
  exact ⟨b2, hb2, hp2.trans hp1, E1 ++ E2, by rw [he2, he1, List.append_assoc]⟩

theorem ExtT.of_adv {ls ls' : LS} {T : Array GIR.Block} (h : ExtT ls' T) (he : ls.Adv ls') : ExtT ls T :=
  h.of_ext he.ext

theorem ExtT.inst {ls : LS} {T : Array GIR.Block} (h : ExtT ls T) {b : BlockId} {blk : BlockB} {p : Nat}
    {i : Inst} (hb : ls.blocks[b]? = some blk) (hi : blk.insts.toList[p]? = some i) :
    instAtT T (b, p) = some i := by
  obtain ⟨b', hb', -, E, he⟩ := h.2 b blk hb
  simp only [instAtT, hb', Option.bind_some]
  rw [he, List.getElem?_append_left (by simpa using (List.getElem?_eq_some_iff.mp hi).1)]
  exact hi

theorem ExtT.params {ls : LS} {T : Array GIR.Block} (h : ExtT ls T) {b : BlockId} {blk : BlockB}
    (hb : ls.blocks[b]? = some blk) : ∃ blk' : GIR.Block, T[b]? = some blk' ∧ blk'.params = blk.params := by
  obtain ⟨b', hb', hp, -⟩ := h.2 b blk hb
  exact ⟨b', hb', hp⟩

theorem LS.pp_eq {ls : LS} {b : BlockId} {blk : BlockB} (hc : ls.cur = some b)
    (hb : ls.blocks[b]? = some blk) : ls.pp = some (b, blk.insts.size) := by
  simp [LS.pp, hc, hb]

theorem LS.pp_some {ls : LS} {pt : Pt} (h : ls.pp = some pt) :
    ∃ blk, ls.cur = some pt.1 ∧ ls.blocks[pt.1]? = some blk ∧ pt.2 = blk.insts.size := by
  unfold LS.pp at h
  cases hc : ls.cur with
  | none => simp [hc] at h
  | some b =>
    cases hb : ls.blocks[b]? with
    | none => simp [hc, hb] at h
    | some blk =>
      simp [hc, hb] at h
      subst h
      exact ⟨blk, rfl, hb, rfl⟩

theorem push_get (blk : BlockB) (i : Inst) : (blk.insts.push i).toList[blk.insts.size]? = some i := by
  simp

/-- Emitting into the current block: what the builder did, and where the instruction now stands. -/
theorem modifyCur_facts {ls : LS} {b : BlockId} {blk : BlockB} (hc : ls.cur = some b)
    (hb : ls.blocks[b]? = some blk) (i : Inst) {T : Array GIR.Block} {vs : Array (Option VTy)}
    {c : Option BlockId} {st : List ScopeId}
    (hext : ExtT { ls with
      blocks := ls.blocks.modify b (fun blk => { blk with insts := blk.insts.push i })
      vals := vs
      cur := c
      stack := st } T) :
    instAtT T (b, blk.insts.size) = some i := by
  refine hext.inst (b := b) (blk := { blk with insts := blk.insts.push i }) ?_ (push_get blk i)
  show (ls.blocks.modify b _)[b]? = _
  rw [Array.getElem?_modify, hb]
  simp

theorem modifyCur_pp {ls : LS} {b : BlockId} {blk : BlockB} (hc : ls.cur = some b)
    (hb : ls.blocks[b]? = some blk) (i : Inst) {vs : Array (Option VTy)} {st : List ScopeId} :
    ({ ls with
      blocks := ls.blocks.modify b (fun blk => { blk with insts := blk.insts.push i })
      vals := vs
      stack := st } : LS).pp = some (b, blk.insts.size + 1) := by
  have hb' : (ls.blocks.modify b (fun blk => { blk with insts := blk.insts.push i }))[b]? =
      some { blk with insts := blk.insts.push i } := by
    rw [Array.getElem?_modify, hb]
    simp
  have := LS.pp_eq (ls := { ls with
      blocks := ls.blocks.modify b (fun blk => { blk with insts := blk.insts.push i })
      vals := vs
      stack := st }) (b := b) (blk := { blk with insts := blk.insts.push i }) hc hb'
  simpa using this

theorem emitDef_facts {op : Op} {le : LEnv} {ls : LS} {r : ValueId} {ls' : LS} {pt : Pt}
    {T : Array GIR.Block} (h : emitDef op le ls = (r, ls')) (hpp : ls.pp = some pt)
    (hext : ExtT ls' T) :
    r = ls.vals.size ∧ ls'.vals.size = ls.vals.size + 1 ∧ ls'.stack = ls.stack ∧
    ls'.pp = some (pt.1, pt.2 + 1) ∧ instAtT T pt = some (.def r op) := by
  obtain ⟨blk, hc, hb, hp⟩ := LS.pp_some hpp
  rw [emitDef_run _ _ hc] at h
  obtain ⟨hr, rfl⟩ := Prod.mk.inj h
  subst hr
  obtain ⟨p1, p2⟩ := pt
  simp only at hc hb hp
  subst hp
  refine ⟨rfl, by simp, rfl, ?_, ?_⟩
  · exact modifyCur_pp hc hb _
  · exact modifyCur_facts hc hb _ hext

theorem emitEffect_facts {e : Effect} {le : LEnv} {ls : LS} {r : Unit} {ls' : LS} {pt : Pt}
    {T : Array GIR.Block} (h : emitEffect e le ls = (r, ls')) (hpp : ls.pp = some pt)
    (hext : ExtT ls' T) :
    ls'.vals.size = ls.vals.size ∧ ls'.stack = ls.stack ∧
    ls'.pp = some (pt.1, pt.2 + 1) ∧ instAtT T pt = some (.eff e) := by
  obtain ⟨blk, hc, hb, hp⟩ := LS.pp_some hpp
  rw [emitEffect_run _ _ hc] at h
  obtain ⟨-, rfl⟩ := Prod.mk.inj h
  obtain ⟨p1, p2⟩ := pt
  simp only at hc hb hp
  subst hp
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact modifyCur_pp hc hb _
  · exact modifyCur_facts hc hb _ hext

theorem emitTerm_facts {t : Term} {le : LEnv} {ls : LS} {r : Unit} {ls' : LS} {pt : Pt}
    {T : Array GIR.Block} (h : emitTerm t le ls = (r, ls')) (hpp : ls.pp = some pt)
    (hext : ExtT ls' T) :
    ls'.vals.size = ls.vals.size ∧ ls'.stack = ls.stack ∧ ls'.cur = none ∧
    instAtT T pt = some (.term t) := by
  obtain ⟨blk, hc, hb, hp⟩ := LS.pp_some hpp
  rw [emitTerm_run _ _ hc] at h
  obtain ⟨-, rfl⟩ := Prod.mk.inj h
  obtain ⟨p1, p2⟩ := pt
  simp only at hc hb hp
  subst hp
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact modifyCur_facts hc hb _ hext

/-! ### Frames -/

/-- A Core environment and a frame, with the builder state, correspond. -/
structure Rel (cfg : Cfg) (env : Env) (cx : FnCtx) (fr : Frame) (ls : LS) : Prop where
  prof : cx.cfg.profile = cfg.profile
  slots : cx.fn.slots = env.vars.mapIdx fun i lv => (⟨lv.ty, lv.kind, lv.scope, i⟩ : Slot)
  act : fr.act = env.act
  scopes : fr.scopes = env.scopes
  depth : fr.depth = env.depth
  stack : ls.stack = env.scopes.map (·.1)

theorem Rel.set {cfg : Cfg} {env : Env} {cx : FnCtx} {fr : Frame} {ls : LS}
    (h : Rel cfg env cx fr ls) (r : ValueId) (x : RVal) : Rel cfg env cx (fr.set r x) ls :=
  ⟨h.prof, h.slots, h.act, h.scopes, h.depth, h.stack⟩

theorem Rel.stack_eq {cfg : Cfg} {env : Env} {cx : FnCtx} {fr : Frame} {ls ls' : LS}
    (h : Rel cfg env cx fr ls) (e : ls'.stack = ls.stack) : Rel cfg env cx fr ls' :=
  ⟨h.prof, h.slots, h.act, h.scopes, h.depth, e.trans h.stack⟩

/-- Cells below `k` are as they were. -/
def Same (k : Nat) (fr fr' : Frame) : Prop := ∀ i, i < k → fr'.vals[i]? = fr.vals[i]?

theorem Same.refl (k : Nat) (fr : Frame) : Same k fr fr := fun _ _ => rfl

theorem Same.trans {k1 k2 : Nat} {a b c : Frame} (h1 : Same k1 a b) (h2 : Same k2 b c)
    (hk : k1 ≤ k2) : Same k1 a c := fun i hi => by
  rw [h2 i (Nat.lt_of_lt_of_le hi hk), h1 i hi]

theorem Same.mono {k k' : Nat} {a b : Frame} (h : Same k a b) (hk : k' ≤ k) : Same k' a b :=
  fun i hi => h i (Nat.lt_of_lt_of_le hi hk)

theorem Same.set {k : Nat} (fr : Frame) {r : ValueId} (hr : k ≤ r) (x : RVal) : Same k fr (fr.set r x) := by
  intro i hi
  have : r ≠ i := fun h => by subst h; exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hi hr)
  simp [Frame.set, Std.HashMap.getElem?_insert, this]

theorem Frame.set_get (fr : Frame) (r : ValueId) (x : RVal) : (fr.set r x).vals[r]? = some x := by
  simp [Frame.set, Std.HashMap.getElem?_insert]

/-- What a fragment leaves behind: where it ended, the cells that carry its result, and that the
frame still agrees with the starting frame below the first value the fragment defined. -/
structure Post (cfg : Cfg) (env : Env) (cx : FnCtx) (ls : LS) (fr : Frame) (ls' : LS) (fr' : Frame)
    (pt' : Pt) (cells : List (ValueId × RVal)) : Prop where
  pp : ls'.pp = some pt'
  has : ∀ p ∈ cells, fr'.vals[p.1]? = some p.2
  lt : ∀ p ∈ cells, p.1 < ls'.vals.size
  mono : ls.vals.size ≤ ls'.vals.size
  same : Same ls.vals.size fr fr'
  rel : Rel cfg env cx fr' ls'

/-- A defining instruction after a fragment: the new cell is the result. -/
theorem Post.def_leaf {cfg : Cfg} {env : Env} {cx : FnCtx} {ls lsk ls1 : LS} {fr frk : Frame}
    {ptk : Pt} {cellsk : List (ValueId × RVal)}
    (hP : Post cfg env cx ls fr lsk frk ptk cellsk) {op : Op} {le : LEnv} {r : ValueId}
    (h : emitDef op le lsk = (r, ls1)) (hext : ExtT ls1 cx.fn.blocks) (x : RVal) :
    Post cfg env cx ls fr ls1 (frk.set r x) (ptk.1, ptk.2 + 1) [(r, x)] ∧
    instAt cx.fn ptk = some (.def r op) := by
  obtain ⟨hr, hv, hst, hpp, hi⟩ := emitDef_facts h hP.pp hext
  have hm := hP.mono
  refine ⟨⟨hpp, ?_, ?_, ?_, ?_, ?_⟩, hi⟩
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact Frame.set_get _ _ _
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    nat_omega
  · nat_omega
  · exact (hP.same.trans (Same.set frk (by nat_omega) x) (Nat.le_refl _))
  · exact (hP.rel.set r x).stack_eq hst

theorem getElem?_push_lt {α : Type} {a : Array α} {x : α} {i : Nat} (h : i < a.size) :
    (a.push x)[i]? = a[i]? := by
  rw [Array.getElem?_push]
  simp [Nat.ne_of_lt h]

theorem getElem?_push_size {α : Type} {a : Array α} {x : α} : (a.push x)[a.size]? = some x := by
  simp

theorem getElem?_modify_ne {α : Type} {a : Array α} {f : α → α} {i j : Nat} (h : i ≠ j) :
    (a.modify i f)[j]? = a[j]? := by
  rw [Array.getElem?_modify]
  simp [h]

theorem LS.pp_cur {ls : LS} {b : BlockId} {blk : BlockB} (hb : ls.blocks[b]? = some blk) :
    ({ ls with cur := some b } : LS).pp = some (b, blk.insts.size) :=
  LS.pp_eq (ls := { ls with cur := some b }) rfl hb

/-- The join after a branch: the frame is the frame at the end of the arm, with the join's
parameter bound. -/
theorem Post.join {cfg : Cfg} {env : Env} {cx : FnCtx} {ls ls' : LS} {fr frj : Frame} {pt' : Pt}
    {p : ValueId} {x : RVal} (hsame : Same ls.vals.size fr frj) (hrel : Rel cfg env cx frj ls)
    (hp : ls.vals.size ≤ p) (hlt : p < ls'.vals.size) (hmono : ls.vals.size ≤ ls'.vals.size)
    (hst : ls'.stack = ls.stack) (hpp : ls'.pp = some pt') :
    Post cfg env cx ls fr ls' (frj.set p x) pt' [(p, x)] := by
  refine ⟨hpp, ?_, ?_, hmono, hsame.trans (Same.set frj hp x) (Nat.le_refl _),
    (hrel.set p x).stack_eq hst⟩
  · intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact Frame.set_get _ _ _
  · intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact hlt

theorem scFork_facts {isAnd : Bool} {x : ValueId} {le : LEnv} {ls : LS} {rb jb p : BlockId}
    {ls' : LS} {pt : Pt} {T : Array GIR.Block}
    (h : scFork isAnd x le ls = ((rb, jb, p), ls')) (hpp : ls.pp = some pt) (hext : ExtT ls' T) :
    rb = ls.blocks.size ∧ jb = ls.blocks.size + 1 ∧ p = ls.vals.size ∧
    ls'.vals.size = ls.vals.size + 1 ∧ ls'.stack = ls.stack ∧ ls'.cur = none ∧
    instAtT T pt = some (.term (scTerm isAnd x rb jb)) ∧
    ls'.blocks[rb]? = some ⟨[], #[]⟩ ∧ ls'.blocks[jb]? = some ⟨[(p, .data .bool)], #[]⟩ := by
  obtain ⟨blk, hc, hb, hp⟩ := LS.pp_some hpp
  have hlt : pt.1 < ls.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  rw [scFork_run _ _ _ hc] at h
  obtain ⟨hids, rfl⟩ := Prod.mk.inj h
  obtain ⟨h1, h2⟩ := Prod.mk.inj hids
  obtain ⟨h2a, h2b⟩ := Prod.mk.inj h2
  subst h1 h2a h2b
  obtain ⟨p1, p2⟩ := pt
  simp only at hc hb hp hlt
  subst hp
  have hb2 : (((ls.blocks.push ⟨[], #[]⟩).push ⟨[(ls.vals.size, .data .bool)], #[]⟩))[p1]? = some blk := by
    rw [getElem?_push_lt (by simp; nat_omega), getElem?_push_lt hlt, hb]
  refine ⟨rfl, rfl, rfl, by simp, rfl, rfl, ?_, ?_, ?_⟩
  · exact modifyCur_facts (ls := { ls with
      blocks := (ls.blocks.push ⟨[], #[]⟩).push ⟨[(ls.vals.size, .data .bool)], #[]⟩
      vals := ls.vals.push (some (.data .bool)) }) (b := p1) (blk := blk) hc hb2 _ hext
  · show (((ls.blocks.push ⟨[], #[]⟩).push ⟨[(ls.vals.size, .data .bool)], #[]⟩).modify p1 _)[ls.blocks.size]? = _
    rw [getElem?_modify_ne (Nat.ne_of_lt hlt), getElem?_push_lt (by simp), getElem?_push_size]
  · show (((ls.blocks.push ⟨[], #[]⟩).push ⟨[(ls.vals.size, .data .bool)], #[]⟩).modify p1 _)[ls.blocks.size + 1]? = _
    rw [getElem?_modify_ne (by nat_omega)]
    have : ls.blocks.size + 1 = (ls.blocks.push (⟨[], #[]⟩ : BlockB)).size := by simp
    rw [this, getElem?_push_size]

/-- A defining instruction after a fragment, keeping the cells the fragment had. -/
theorem Post.def_leaf_keep {cfg : Cfg} {env : Env} {cx : FnCtx} {ls lsk ls1 : LS} {fr frk : Frame}
    {ptk : Pt} {cellsk : List (ValueId × RVal)}
    (hP : Post cfg env cx ls fr lsk frk ptk cellsk) {op : Op} {le : LEnv} {r : ValueId}
    (h : emitDef op le lsk = (r, ls1)) (hext : ExtT ls1 cx.fn.blocks) (x : RVal) :
    Post cfg env cx ls fr ls1 (frk.set r x) (ptk.1, ptk.2 + 1) ((r, x) :: cellsk) ∧
    instAt cx.fn ptk = some (.def r op) := by
  obtain ⟨hr, hv, hst, hpp, hi⟩ := emitDef_facts h hP.pp hext
  have hm := hP.mono
  refine ⟨⟨hpp, ?_, ?_, ?_, ?_, ?_⟩, hi⟩
  · intro p hp
    rcases List.mem_cons.mp hp with hp | hp
    · subst hp; exact Frame.set_get _ _ _
    · have hne : r ≠ p.1 := by have := hP.lt p hp; nat_omega
      simp only [Frame.set, Std.HashMap.getElem?_insert, hne, beq_iff_eq, ↓reduceIte]
      exact hP.has p hp
  · intro p hp
    rcases List.mem_cons.mp hp with hp | hp
    · subst hp; nat_omega
    · have := hP.lt p hp; nat_omega
  · nat_omega
  · exact (hP.same.trans (Same.set frk (by nat_omega) x) (Nat.le_refl _))
  · exact (hP.rel.set r x).stack_eq hst

/-! ### Joins -/

/-- What `patchBrs` does to a state: the blocks named get a branch to the join; nothing else
changes. -/
theorem patchBrs_facts {jb : BlockId} : ∀ (live : List (BlockId × ValueId)) {le : LEnv} {ls1 ls2 : LS}
    {u : Unit}, patchBrs jb live le ls1 = (u, ls2) → (live.map Prod.fst).Nodup →
    ls2.vals = ls1.vals ∧ ls2.cur = ls1.cur ∧ ls2.stack = ls1.stack ∧
    (∀ i, (∀ p ∈ live, p.1 ≠ i) → ls2.blocks[i]? = ls1.blocks[i]?) ∧
    (∀ b v blk, (b, v) ∈ live → ls1.blocks[b]? = some blk →
      ls2.blocks[b]? = some { blk with insts := blk.insts.push (.term (.br jb [v])) }) ∧
    ls2.blocks.size = ls1.blocks.size
  | [], le, ls1, ls2, u, hp, _ => by
    unfold patchBrs at hp
    rw [pure_run] at hp
    obtain ⟨-, rfl⟩ := Prod.mk.inj hp
    exact ⟨rfl, rfl, rfl, fun _ _ => rfl, fun b v blk hm => absurd hm (by simp), rfl⟩
  | (b, v) :: rest, le, ls1, ls2, u, hp, hnd => by
    unfold patchBrs at hp
    obtain ⟨u1, ls3, h1, h2⟩ := bind_eq.mp hp
    rw [patchTerm_run] at h1
    obtain ⟨-, rfl⟩ := Prod.mk.inj h1
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨hb, hnd'⟩ := hnd
    obtain ⟨hv, hc, hst, hkeep, hset, hsz⟩ := patchBrs_facts rest h2 hnd'
    refine ⟨hv, hc, hst, fun i hi => ?_, fun b' v' blk hm hb' => ?_, by simpa using hsz⟩
    · rw [hkeep i (fun p hp => hi p (by simp [hp]))]
      show (ls1.blocks.modify b _)[i]? = _
      rw [getElem?_modify_ne (hi (b, v) (by simp))]
    · rcases List.mem_cons.mp hm with hm | hm
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hm
        have hne : ∀ p ∈ rest, p.1 ≠ b' := fun p hp h => hb ⟨p, hp, h.symm ▸ rfl⟩ |>.elim
        rw [hkeep b' (fun p hp => fun h => hb ⟨p, hp, h⟩)]
        show (ls1.blocks.modify b' _)[b']? = _
        rw [Array.getElem?_modify, hb']
        simp
      · have hne : b ≠ b' := fun h => hb ⟨(b', v'), hm, h.symm⟩
        apply hset b' v' blk hm
        show (ls1.blocks.modify b _)[b']? = _
        rw [getElem?_modify_ne hne]
        exact hb'

theorem joinTail_facts {live : List (BlockId × ValueId)} {le : LEnv} {ls : LS} {r : ValueId}
    {ls' : LS} {T : Array GIR.Block}
    (h : (do
        let ty ← valTy (live.headD (0, 0)).2
        let (jb, js) ← newBlock [ty]
        patchBrs jb live
        setCur (some jb)
        pure (js.headD 0) : B ValueId) le ls = (r, ls'))
    (hnd : (live.map Prod.fst).Nodup) (hlt : ∀ p ∈ live, p.1 < ls.blocks.size) (hext : ExtT ls' T) :
    ∃ ty, r = ls.vals.size ∧ ls'.vals.size = ls.vals.size + 1 ∧ ls'.stack = ls.stack ∧
      ls'.blocks[ls.blocks.size]? = some ⟨[(ls.vals.size, ty)], #[]⟩ ∧ ls'.cur = some ls.blocks.size ∧
      (∀ b v blk, (b, v) ∈ live → ls.blocks[b]? = some blk →
        instAtT T (b, blk.insts.size) = some (.term (.br ls.blocks.size [v]))) := by
  simp only [bind_eq] at h
  obtain ⟨ty, ls2, h1, ⟨jb, js⟩, ls3, h2, u, ls4, h3, u2, ls5, h4, hp⟩ := h
  have hls2 : ls2 = ls := valTy_eq h1
  subst hls2
  rw [newBlock1_run] at h2
  obtain ⟨he, rfl⟩ := Prod.mk.inj h2
  obtain ⟨hj, hjs⟩ := Prod.mk.inj he
  obtain ⟨hv, hc, hst, hkeep, hset, hsz⟩ := patchBrs_facts live h3 hnd
  rw [setCur_run] at h4
  obtain ⟨-, rfl⟩ := Prod.mk.inj h4
  rw [pure_run] at hp
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
  subst hj hjs
  dsimp only at hv hst hkeep hsz hext ⊢
  have hjb4 : ls4.blocks[ls2.blocks.size]? = some ⟨[(ls2.vals.size, ty)], #[]⟩ := by
    rw [hkeep ls2.blocks.size (fun p hp h => by
      have := hlt p hp
      rw [h] at this
      exact Nat.lt_irrefl _ this)]
    simp
  refine ⟨ty, rfl, ?_, ?_, hjb4, rfl, ?_⟩
  · simp [hv]
  · simp [hst]
  · intro b v blk hm hb
    have hbl := hlt (b, v) hm
    have hb1 : (ls2.blocks.push (⟨[(ls2.vals.size, ty)], #[]⟩ : BlockB))[b]? = some blk := by
      rw [getElem?_push_lt hbl]; exact hb
    have hb4 := hset b v blk hm hb1
    have hi := hext.inst (b := b) (blk := { blk with insts := blk.insts.push (.term (.br ls2.blocks.size [v])) })
      hb4 (push_get blk _)
    exact hi

theorem joinValue_facts {endT endF : Option BlockId} {vt vf : ValueId} {le : LEnv} {ls : LS}
    {r : ValueId} {ls' : LS} {T : Array GIR.Block}
    (h : joinValue endT vt endF vf le ls = (r, ls')) (hext : ExtT ls' T)
    (hlive : endT.isSome ∨ endF.isSome)
    (hnd : ∀ bT bF, endT = some bT → endF = some bF → bT ≠ bF)
    (hltT : ∀ b, endT = some b → b < ls.blocks.size) (hltF : ∀ b, endF = some b → b < ls.blocks.size) :
    ∃ ty, r = ls.vals.size ∧ ls'.vals.size = ls.vals.size + 1 ∧ ls'.stack = ls.stack ∧
      ls'.blocks[ls.blocks.size]? = some ⟨[(ls.vals.size, ty)], #[]⟩ ∧ ls'.cur = some ls.blocks.size ∧
      (∀ b blk, endT = some b → ls.blocks[b]? = some blk →
        instAtT T (b, blk.insts.size) = some (.term (.br ls.blocks.size [vt]))) ∧
      (∀ b blk, endF = some b → ls.blocks[b]? = some blk →
        instAtT T (b, blk.insts.size) = some (.term (.br ls.blocks.size [vf]))) := by
  unfold joinValue at h
  cases endT with
  | none =>
    cases endF with
    | none => simp at hlive
    | some bF =>
      obtain ⟨ty, h1, h2, h3, h4, h5, h6⟩ := joinTail_facts (live := [(bF, vf)]) h (by simp)
        (by intro p hp; simp at hp; subst hp; exact hltF bF rfl) hext
      refine ⟨ty, h1, h2, h3, h4, h5, fun b blk hb => by simp at hb, fun b blk hb hblk => ?_⟩
      simp at hb; subst hb
      exact h6 bF vf blk (by simp) hblk
  | some bT =>
    cases endF with
    | none =>
      obtain ⟨ty, h1, h2, h3, h4, h5, h6⟩ := joinTail_facts (live := [(bT, vt)]) h (by simp)
        (by intro p hp; simp at hp; subst hp; exact hltT bT rfl) hext
      refine ⟨ty, h1, h2, h3, h4, h5, fun b blk hb hblk => ?_, fun b blk hb => by simp at hb⟩
      simp at hb; subst hb
      exact h6 bT vt blk (by simp) hblk
    | some bF =>
      obtain ⟨ty, h1, h2, h3, h4, h5, h6⟩ := joinTail_facts (live := [(bT, vt), (bF, vf)]) h
        (by simpa using hnd bT bF rfl rfl)
        (by intro p hp; simp at hp; rcases hp with rfl | rfl; exact hltT _ rfl; exact hltF _ rfl) hext
      refine ⟨ty, h1, h2, h3, h4, h5, fun b blk hb hblk => ?_, fun b blk hb hblk => ?_⟩
      · simp at hb; subst hb
        exact h6 bT vt blk (by simp) hblk
      · simp at hb; subst hb
        exact h6 bF vf blk (by simp) hblk

theorem patchBrs0_facts {jb : BlockId} : ∀ (live : List BlockId) {le : LEnv} {ls1 ls2 : LS}
    {u : Unit}, patchBrs0 jb live le ls1 = (u, ls2) → live.Nodup →
    ls2.vals = ls1.vals ∧ ls2.cur = ls1.cur ∧ ls2.stack = ls1.stack ∧
    (∀ i, (∀ p ∈ live, p ≠ i) → ls2.blocks[i]? = ls1.blocks[i]?) ∧
    (∀ b blk, b ∈ live → ls1.blocks[b]? = some blk →
      ls2.blocks[b]? = some { blk with insts := blk.insts.push (.term (.br jb [])) }) ∧
    ls2.blocks.size = ls1.blocks.size
  | [], le, ls1, ls2, u, hp, _ => by
    unfold patchBrs0 at hp
    rw [pure_run] at hp
    obtain ⟨-, rfl⟩ := Prod.mk.inj hp
    exact ⟨rfl, rfl, rfl, fun _ _ => rfl, fun b blk hm => absurd hm (by simp), rfl⟩
  | b :: rest, le, ls1, ls2, u, hp, hnd => by
    unfold patchBrs0 at hp
    obtain ⟨u1, ls3, h1, h2⟩ := bind_eq.mp hp
    rw [patchTerm_run] at h1
    obtain ⟨-, rfl⟩ := Prod.mk.inj h1
    simp only [List.nodup_cons] at hnd
    obtain ⟨hb, hnd'⟩ := hnd
    obtain ⟨hv, hc, hst, hkeep, hset, hsz⟩ := patchBrs0_facts rest h2 hnd'
    refine ⟨hv, hc, hst, fun i hi => ?_, fun b' blk hm hb' => ?_, by simpa using hsz⟩
    · rw [hkeep i (fun p hp => hi p (by simp [hp]))]
      show (ls1.blocks.modify b _)[i]? = _
      rw [getElem?_modify_ne (hi b (by simp))]
    · rcases List.mem_cons.mp hm with hm | hm
      · subst hm
        rw [hkeep b' (fun p hp => fun h => hb (h ▸ hp))]
        show (ls1.blocks.modify b' _)[b']? = _
        rw [Array.getElem?_modify, hb']
        simp
      · have hne : b ≠ b' := fun h => hb (h ▸ hm)
        apply hset b' blk hm
        show (ls1.blocks.modify b _)[b']? = _
        rw [getElem?_modify_ne hne]
        exact hb'

theorem joinArms_facts {endT endF : Option BlockId} {le : LEnv} {ls : LS} {r : Unit} {ls' : LS}
    {T : Array GIR.Block}
    (h : joinArms endT endF le ls = (r, ls')) (hext : ExtT ls' T)
    (hlive : endT.isSome ∨ endF.isSome)
    (hnd : ∀ bT bF, endT = some bT → endF = some bF → bT ≠ bF)
    (hltT : ∀ b, endT = some b → b < ls.blocks.size) (hltF : ∀ b, endF = some b → b < ls.blocks.size) :
    ls'.vals.size = ls.vals.size ∧ ls'.stack = ls.stack ∧
      ls'.blocks[ls.blocks.size]? = some ⟨[], #[]⟩ ∧ ls'.cur = some ls.blocks.size ∧
      (∀ b blk, (endT = some b ∨ endF = some b) → ls.blocks[b]? = some blk →
        instAtT T (b, blk.insts.size) = some (.term (.br ls.blocks.size []))) := by
  have key : ∀ {live : List BlockId}, live.Nodup → (∀ p ∈ live, p < ls.blocks.size) →
      (do
        let (jb, _) ← newBlock []
        patchBrs0 jb live
        setCur (some jb) : B Unit) le ls = (r, ls') →
      ls'.vals.size = ls.vals.size ∧ ls'.stack = ls.stack ∧
      ls'.blocks[ls.blocks.size]? = some ⟨[], #[]⟩ ∧ ls'.cur = some ls.blocks.size ∧
      (∀ b blk, b ∈ live → ls.blocks[b]? = some blk →
        instAtT T (b, blk.insts.size) = some (.term (.br ls.blocks.size []))) := by
    intro live hnd hlt hk
    simp only [bind_eq] at hk
    obtain ⟨⟨jb, js⟩, ls3, h2, u, ls4, h3, h4⟩ := hk
    rw [newBlock0_run] at h2
    obtain ⟨he, rfl⟩ := Prod.mk.inj h2
    obtain ⟨hj, hjs⟩ := Prod.mk.inj he
    obtain ⟨hv, hc, hst, hkeep, hset, hsz⟩ := patchBrs0_facts live h3 hnd
    rw [setCur_run] at h4
    obtain ⟨-, rfl⟩ := Prod.mk.inj h4
    subst hj
    dsimp only at hv hst hkeep hsz hext ⊢
    have hjb4 : ls4.blocks[ls.blocks.size]? = some ⟨[], #[]⟩ := by
      rw [hkeep ls.blocks.size (fun p hp h => by
        have := hlt p hp
        rw [h] at this
        exact Nat.lt_irrefl _ this)]
      simp
    refine ⟨by simp [hv], by simp [hst], hjb4, rfl, ?_⟩
    intro b blk hm hb
    have hbl := hlt b hm
    have hb1 : (ls.blocks.push (⟨[], #[]⟩ : BlockB))[b]? = some blk := by
      rw [getElem?_push_lt hbl]; exact hb
    have hb4 := hset b blk hm hb1
    exact hext.inst (b := b) (blk := { blk with insts := blk.insts.push (.term (.br ls.blocks.size [])) })
      hb4 (push_get blk _)
  unfold joinArms at h
  cases endT with
  | none =>
    cases endF with
    | none => simp at hlive
    | some bF =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := key (live := [bF]) (by simp)
        (by intro p hp; simp at hp; rw [hp]; exact hltF bF rfl) h
      refine ⟨h1, h2, h3, h4, fun b blk hb hblk => ?_⟩
      rcases hb with hb | hb
      · simp at hb
      · simp at hb; subst hb; exact h5 bF blk (by simp) hblk
  | some bT =>
    cases endF with
    | none =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := key (live := [bT]) (by simp)
        (by intro p hp; simp at hp; rw [hp]; exact hltT bT rfl) h
      refine ⟨h1, h2, h3, h4, fun b blk hb hblk => ?_⟩
      rcases hb with hb | hb
      · simp at hb; subst hb; exact h5 bT blk (by simp) hblk
      · simp at hb
    | some bF =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := key (live := [bT, bF]) (by simpa using hnd bT bF rfl rfl)
        (by intro p hp; simp at hp; rcases hp with rfl | rfl; exact hltT _ rfl; exact hltF _ rfl) h
      refine ⟨h1, h2, h3, h4, fun b blk hb hblk => ?_⟩
      rcases hb with hb | hb
      · simp at hb; subst hb; exact h5 bT blk (by simp) hblk
      · simp at hb; subst hb; exact h5 bF blk (by simp) hblk

theorem fork_facts {cv : ValueId} {le : LEnv} {ls : LS} {tb eb : BlockId} {ls' : LS} {pt : Pt}
    {T : Array GIR.Block} (h : fork cv le ls = ((tb, eb), ls')) (hpp : ls.pp = some pt)
    (hext : ExtT ls' T) :
    tb = ls.blocks.size ∧ eb = ls.blocks.size + 1 ∧ ls'.blocks.size = ls.blocks.size + 2 ∧
    ls'.vals = ls.vals ∧ ls'.stack = ls.stack ∧ ls'.cur = none ∧
    instAtT T pt = some (.term (.condbr cv tb [] eb [])) ∧
    ls'.blocks[tb]? = some ⟨[], #[]⟩ ∧ ls'.blocks[eb]? = some ⟨[], #[]⟩ := by
  obtain ⟨blk, hc, hb, hp⟩ := LS.pp_some hpp
  have hlt : pt.1 < ls.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
  rw [fork_run _ _ hc] at h
  obtain ⟨hids, rfl⟩ := Prod.mk.inj h
  obtain ⟨h1, h2⟩ := Prod.mk.inj hids
  subst h1 h2
  obtain ⟨p1, p2⟩ := pt
  simp only at hc hb hp hlt
  subst hp
  have hb2 : ((ls.blocks.push (⟨[], #[]⟩ : BlockB)).push (⟨[], #[]⟩ : BlockB))[p1]? = some blk := by
    rw [getElem?_push_lt (by simp; nat_omega), getElem?_push_lt hlt, hb]
  refine ⟨rfl, rfl, by simp, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact modifyCur_facts (ls := { ls with blocks := (ls.blocks.push ⟨[], #[]⟩).push ⟨[], #[]⟩ })
      (b := p1) (blk := blk) hc hb2 _ hext
  · show (((ls.blocks.push ⟨[], #[]⟩).push ⟨[], #[]⟩).modify p1 _)[ls.blocks.size]? = _
    rw [getElem?_modify_ne (Nat.ne_of_lt hlt), getElem?_push_lt (by simp), getElem?_push_size]
  · show (((ls.blocks.push ⟨[], #[]⟩).push ⟨[], #[]⟩).modify p1 _)[ls.blocks.size + 1]? = _
    rw [getElem?_modify_ne (by nat_omega)]
    have : ls.blocks.size + 1 = (ls.blocks.push (⟨[], #[]⟩ : BlockB)).size := by simp
    rw [this, getElem?_push_size]

theorem joinValue_ext {endT endF : Option BlockId} {vt vf : ValueId} {le : LEnv} {ls : LS}
    {r : ValueId} {ls' : LS} (h : joinValue endT vt endF vf le ls = (r, ls')) : ls.Ext ls' := by
  unfold joinValue at h
  have key : ∀ {live : List (BlockId × ValueId)},
      (do
        let ty ← valTy (live.headD (0, 0)).2
        let (jb, js) ← newBlock [ty]
        patchBrs jb live
        setCur (some jb)
        pure (js.headD 0) : B ValueId) le ls = (r, ls') → ls.Ext ls' := by
    intro live hk
    simp only [bind_eq] at hk
    obtain ⟨ty, ls2, h1, ⟨jb, js⟩, ls3, h2, u, ls4, h3, u2, ls5, h4, hp⟩ := hk
    have hls2 : ls2 = ls := valTy_eq h1
    subst hls2
    have e2 := (adv_newBlock1 h2).ext
    have e3 := adv_patchBrs_ext live h3
    rw [setCur_run] at h4
    obtain ⟨-, rfl⟩ := Prod.mk.inj h4
    rw [pure_run] at hp
    obtain ⟨-, rfl⟩ := Prod.mk.inj hp
    exact e2.trans e3
  cases endT <;> cases endF
  · simp only [bind_eq] at h
    obtain ⟨u, ls2, h1, hp⟩ := h
    rw [setCur_run] at h1
    obtain ⟨-, rfl⟩ := Prod.mk.inj h1
    rw [pure_run] at hp
    obtain ⟨-, rfl⟩ := Prod.mk.inj hp
    exact LS.Ext.refl _
  all_goals exact key h

theorem joinArms_ext {endT endF : Option BlockId} {le : LEnv} {ls : LS} {r : Unit} {ls' : LS}
    (h : joinArms endT endF le ls = (r, ls')) : ls.Ext ls' := by
  unfold joinArms at h
  have key : ∀ {live : List BlockId},
      (do
        let (jb, _) ← newBlock []
        patchBrs0 jb live
        setCur (some jb) : B Unit) le ls = (r, ls') → ls.Ext ls' := by
    intro live hk
    simp only [bind_eq] at hk
    obtain ⟨⟨jb, js⟩, ls3, h2, u, ls4, h3, h4⟩ := hk
    have e2 := (adv_newBlock0 h2).ext
    have e3 := adv_patchBrs0_ext live h3
    rw [setCur_run] at h4
    obtain ⟨-, rfl⟩ := Prod.mk.inj h4
    exact e2.trans e3
  cases endT <;> cases endF
  · simp only [bind_eq] at h
    rw [setCur_run] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h
    exact LS.Ext.refl _
  all_goals exact key h

/-- The shape of two arms entered from a fork. -/
theorem branch_facts {cv : ValueId} {le : LEnv} {ls1 lsf ls2 ls3 ls5 ls6 : LS} {tb eb : BlockId}
    {pt1 : Pt} {T : Array GIR.Block}
    (hf : fork cv le ls1 = ((tb, eb), lsf)) (hs1 : setCur (some tb) le lsf = ((), ls2))
    (ha1 : ls2.Adv ls3) (hs2 : setCur (some eb) le ls3 = ((), ls5)) (ha2 : ls5.Adv ls6)
    (hpp1 : ls1.pp = some pt1) (hext6 : ExtT ls6 T) :
    tb = ls1.blocks.size ∧ eb = ls1.blocks.size + 1 ∧
    instAtT T pt1 = some (.term (.condbr cv tb [] eb [])) ∧
    (∃ blk, T[tb]? = some blk ∧ blk.params = []) ∧ (∃ blk, T[eb]? = some blk ∧ blk.params = []) ∧
    ls2.pp = some (tb, 0) ∧ ls5.pp = some (eb, 0) ∧
    ls2.stack = ls1.stack ∧ ls2.vals.size = ls1.vals.size ∧ ls3.stack = ls1.stack ∧
    ls6.stack = ls1.stack ∧ ls1.vals.size ≤ ls6.vals.size ∧ ls3.vals.size ≤ ls6.vals.size ∧
    (∀ b, ls3.cur = some b → b < ls3.blocks.size ∧ b ≠ eb ∧ (b = tb ∨ ls1.blocks.size + 2 ≤ b)) ∧
    (∀ b, ls6.cur = some b → b < ls6.blocks.size ∧ (b = eb ∨ ls3.blocks.size ≤ b)) ∧
    (∀ b blk, ls3.blocks[b]? = some blk → b ≠ eb → ls6.blocks[b]? = some blk) ∧
    ls3.blocks.size ≤ ls6.blocks.size ∧ ls6.blocks.size ≥ ls1.blocks.size + 2 := by
  have hs1' := hs1
  rw [setCur_run] at hs1'
  obtain ⟨-, rfl⟩ := Prod.mk.inj hs1'
  have hs2' := hs2
  rw [setCur_run] at hs2'
  obtain ⟨-, rfl⟩ := Prod.mk.inj hs2'
  have hext5 : ExtT { ls3 with cur := some eb } T := hext6.of_adv ha2
  have hext3 : ExtT ls3 T := hext5
  have hext2 : ExtT { lsf with cur := some tb } T := hext3.of_adv ha1
  have hextf : ExtT lsf T := hext2
  obtain ⟨htb, heb, hszf, hvf, hstf, hcf, hinst, hbtb, hbeb⟩ := fork_facts hf hpp1 hextf
  have hext_tb := hextf.params hbtb
  have hext_eb := hextf.params hbeb
  have hpp2 : ({ lsf with cur := some tb } : LS).pp = some (tb, 0) := LS.pp_cur hbtb
  have hbeb3 : ls3.blocks[eb]? = some ⟨[], #[]⟩ := by
    refine ha1.keep eb ⟨[], #[]⟩ ?_ hbeb
    show some tb ≠ some eb
    intro hh
    have := Option.some.inj hh
    nat_omega
  have hpp5 : ({ ls3 with cur := some eb } : LS).pp = some (eb, 0) := LS.pp_cur hbeb3
  have hsz23 := ha1.ext.1
  have hsz56 := ha2.ext.1
  have hv23 := ha1.vals
  have hv56 := ha2.vals
  have hst23 := ha1.stack
  have hst56 := ha2.stack
  refine ⟨htb, heb, ?_, hext_tb, hext_eb, hpp2, hpp5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htb, heb] at hinst ⊢; exact hinst
  · exact hstf
  · show lsf.vals.size = _; rw [hvf]
  · rw [hst23]; exact hstf
  · rw [hst56]; show ls3.stack = _; rw [hst23]; exact hstf
  · show ls1.vals.size ≤ ls6.vals.size
    have : lsf.vals.size = ls1.vals.size := by rw [hvf]
    nat_omega
  · show ls3.vals.size ≤ ls6.vals.size
    exact hv56
  · intro b hb
    rcases ha1.cur with h | h | ⟨c, hc, hc1, hc2⟩
    · rw [hb] at h; cases h
    · rw [hb] at h
      have hbt : b = tb := (Option.some.inj h)
      refine ⟨by show _ < ls3.blocks.size; nat_omega, by nat_omega, Or.inl hbt⟩
    · rw [hb] at hc
      have hbc : b = c := Option.some.inj hc
      rw [hbc]
      refine ⟨hc2, by nat_omega, Or.inr (by nat_omega)⟩
  · intro b hb
    rcases ha2.cur with h | h | ⟨c, hc, hc1, hc2⟩
    · rw [hb] at h; cases h
    · rw [hb] at h
      have hbe : b = eb := Option.some.inj h
      refine ⟨by nat_omega, Or.inl hbe⟩
    · rw [hb] at hc
      have hbc : b = c := Option.some.inj hc
      rw [hbc]
      exact ⟨hc2, Or.inr hc1⟩
  · intro b blk hb hne
    refine ha2.keep b blk ?_ hb
    show some eb ≠ some b
    intro hh; exact hne (Option.some.inj hh).symm
  · show ls3.blocks.size ≤ ls6.blocks.size
    exact hsz56
  · nat_omega

end Goose.Lower
