import Goose.Lower.CoreToGir

/-!
What the lowering's builder does to its state, independent of any run.

A fragment of the lowering starts with some block current. It appends
instructions to that block and to blocks it creates, and it patches a
terminator onto the end of an open block it created. It never touches another
block that already existed. `LS.Adv` states this for a pair of builder states;
it is a preorder, so a fragment built from smaller ones satisfies it by
chaining. The final block table of a function therefore extends the table at
every point of the lowering, which is what lets a proof about the instructions
a fragment emitted be read off the finished function.
-/

namespace Goose.Lower

open Goose.Core
open Goose.GIR (ValueId BlockId SlotId ScopeId FnId VTy Bnd PrintPart Op Effect Term Inst)

/-- `omega`, after exposing that block ids are natural numbers. -/
macro "nat_omega" : tactic => `(tactic| ((try dsimp only [BlockId, ValueId, SlotId, ScopeId, FnId] at *); omega))

/-! ### Running the primitives -/

@[simp] theorem get_apply (le : LEnv) (ls : LS) : (get : B LS) le ls = (ls, ls) := rfl
@[simp] theorem getThe_apply (le : LEnv) (ls : LS) : (getThe LS : B LS) le ls = (ls, ls) := rfl
@[simp] theorem readThe_apply (le : LEnv) (ls : LS) : (readThe LEnv : B LEnv) le ls = (le, ls) := rfl
@[simp] theorem read_apply (le : LEnv) (ls : LS) : (read : B LEnv) le ls = (le, ls) := rfl

theorem bind_run (x : B α) (f : α → B β) (le : LEnv) (ls : LS) :
    (x >>= f) le ls = f (x le ls).1 le (x le ls).2 := rfl

theorem pure_run (a : α) (le : LEnv) (ls : LS) : (pure a : B α) le ls = (a, ls) := rfl

theorem bind_eq {x : B α} {f : α → B β} {le : LEnv} {ls : LS} {r : β} {ls' : LS} :
    (x >>= f) le ls = (r, ls') ↔ ∃ a ls1, x le ls = (a, ls1) ∧ f a le ls1 = (r, ls') := by
  show (match x le ls with | (a, s1) => f a le s1) = (r, ls') ↔ _
  constructor
  · intro h
    exact ⟨(x le ls).1, (x le ls).2, rfl, h⟩
  · rintro ⟨a, ls1, hx, hf⟩
    rw [hx]
    exact hf

theorem pure_eq {a : α} {le : LEnv} {ls : LS} {r : α} {ls' : LS} :
    (pure a : B α) le ls = (r, ls') ↔ a = r ∧ ls = ls' := by
  show (a, ls) = (r, ls') ↔ _
  simp [Prod.ext_iff]

theorem newBlock0_run (le : LEnv) (ls : LS) :
    newBlock [] le ls = ((ls.blocks.size, []), { ls with blocks := ls.blocks.push ⟨[], #[]⟩ }) := rfl

theorem newBlock1_run (t : VTy) (le : LEnv) (ls : LS) :
    newBlock [t] le ls = ((ls.blocks.size, [ls.vals.size]),
      { ls with blocks := ls.blocks.push ⟨[(ls.vals.size, t)], #[]⟩, vals := ls.vals.push (some t) }) := rfl

theorem emitDef_run (op : Op) (le : LEnv) {ls : LS} {b : BlockId} (h : ls.cur = some b) :
    emitDef op le ls = (ls.vals.size,
      { ls with
        vals := ls.vals.push (some (((op.resultTy (tyEnv le ls)).toOption).getD (.data .unit)))
        blocks := ls.blocks.modify b fun blk => { blk with insts := blk.insts.push (.def ls.vals.size op) } }) := by
  unfold emitDef
  simp [h, bind, pure, modify, modifyGet, MonadStateOf.modifyGet, pushInst]

theorem emitEffect_run (e : Effect) (le : LEnv) {ls : LS} {b : BlockId} (h : ls.cur = some b) :
    emitEffect e le ls = ((),
      { ls with blocks := ls.blocks.modify b fun blk => { blk with insts := blk.insts.push (.eff e) } }) := by
  unfold emitEffect
  simp [h, bind, curBlock, pure, modify, modifyGet, MonadStateOf.modifyGet, pushInst]

theorem emitTerm_run (t : Term) (le : LEnv) {ls : LS} {b : BlockId} (h : ls.cur = some b) :
    emitTerm t le ls = ((),
      { ls with blocks := ls.blocks.modify b (fun blk => { blk with insts := blk.insts.push (.term t) }),
                cur := none }) := by
  unfold emitTerm
  simp [h, bind, curBlock, pure, modify, modifyGet, MonadStateOf.modifyGet, pushInst, setCur]

theorem emitDef_none (op : Op) (le : LEnv) {ls : LS} (h : ls.cur = none) : emitDef op le ls = (0, ls) := by
  unfold emitDef; simp [h, bind, pure]

theorem emitEffect_none (e : Effect) (le : LEnv) {ls : LS} (h : ls.cur = none) :
    emitEffect e le ls = ((), ls) := by
  unfold emitEffect; simp [h, bind, curBlock, pure]

theorem emitTerm_none (t : Term) (le : LEnv) {ls : LS} (h : ls.cur = none) :
    emitTerm t le ls = ((), ls) := by
  unfold emitTerm; simp [h, bind, curBlock, pure]

theorem patchTerm_run (b : BlockId) (t : Term) (le : LEnv) (ls : LS) :
    patchTerm b t le ls = ((), { ls with
      blocks := ls.blocks.modify b (fun blk => { blk with insts := blk.insts.push (.term t) }) }) := by
  unfold patchTerm
  simp [pushInst, modify, modifyGet, MonadStateOf.modifyGet]

theorem setCur_run (c : Option BlockId) (le : LEnv) (ls : LS) :
    setCur c le ls = ((), { ls with cur := c }) := by
  unfold setCur; simp [modify, modifyGet, MonadStateOf.modifyGet]

theorem pushScope_run (sc : ScopeId) (le : LEnv) (ls : LS) :
    pushScope sc le ls = ((), { ls with stack := sc :: ls.stack }) := by
  unfold pushScope; simp [modify, modifyGet, MonadStateOf.modifyGet]

theorem popScope_run (le : LEnv) (ls : LS) :
    popScope le ls = ((), { ls with stack := ls.stack.drop 1 }) := by
  unfold popScope; simp [modify, modifyGet, MonadStateOf.modifyGet]

theorem curBlock_run (le : LEnv) (ls : LS) : curBlock le ls = (ls.cur, ls) := by
  unfold curBlock; simp [pure, bind]

theorem whenLive_none (d : α) (k : BlockId → B α) (le : LEnv) {ls : LS} (h : ls.cur = none) :
    whenLive d k le ls = (d, ls) := by
  unfold whenLive; simp [curBlock_run, h, bind, pure]

theorem whenLive_some (d : α) (k : BlockId → B α) (le : LEnv) {ls : LS} {b : BlockId}
    (h : ls.cur = some b) : whenLive d k le ls = k b le ls := by
  unfold whenLive; simp [curBlock_run, h, bind, pure]

theorem fork_run (cv : ValueId) (le : LEnv) {ls : LS} {b : BlockId} (h : ls.cur = some b) :
    fork cv le ls = ((ls.blocks.size, ls.blocks.size + 1),
      { ls with
        blocks := (ls.blocks.push ⟨[], #[]⟩ |>.push ⟨[], #[]⟩).modify b fun blk =>
          { blk with insts := blk.insts.push (.term (.condbr cv ls.blocks.size [] (ls.blocks.size + 1) [])) }
        cur := none }) := by
  unfold fork
  simp only [bind_run, newBlock0_run, Array.size_push, pure_run]
  rw [emitTerm_run _ _ (by simpa using h)]

/-- The terminator of a short-circuit branch. -/
def scTerm (isAnd : Bool) (x : ValueId) (rb jb : BlockId) : Term :=
  if isAnd then .condbr x rb [] jb [x] else .condbr x jb [x] rb []

theorem scFork_run (isAnd : Bool) (x : ValueId) (le : LEnv) {ls : LS} {b : BlockId}
    (h : ls.cur = some b) :
    scFork isAnd x le ls = ((ls.blocks.size, ls.blocks.size + 1, ls.vals.size),
      { ls with
        blocks := ((ls.blocks.push ⟨[], #[]⟩).push ⟨[(ls.vals.size, .data .bool)], #[]⟩).modify b (fun blk => { blk with insts := blk.insts.push (.term (scTerm isAnd x ls.blocks.size (ls.blocks.size + 1))) })
        vals := ls.vals.push (some (.data .bool))
        cur := none }) := by
  unfold scFork
  cases isAnd <;>
  · simp only [bind_run, newBlock0_run, newBlock1_run, Array.size_push, pure_run, ite_true, ite_false,
      Bool.false_eq_true, ↓reduceIte, if_true, if_false]
    rw [emitTerm_run _ _ (by simpa using h)]
    simp [scTerm]

/-! ### The relation -/

/-- The blocks of `ls` as a prefix of the blocks of `ls'`: every block keeps its parameters and
its instructions, and may only gain instructions at the end. -/
def LS.Ext (ls ls' : LS) : Prop :=
  ls.blocks.size ≤ ls'.blocks.size ∧
  ∀ (i : Nat) (blk : BlockB), ls.blocks[i]? = some blk → ∃ blk' : BlockB, ls'.blocks[i]? = some blk' ∧
    blk'.params = blk.params ∧ ∃ E, blk'.insts.toList = blk.insts.toList ++ E

theorem LS.Ext.refl (ls : LS) : ls.Ext ls :=
  ⟨Nat.le_refl _, fun _ blk h => ⟨blk, h, rfl, [], by simp⟩⟩

theorem LS.Ext.trans {a b c : LS} (h1 : a.Ext b) (h2 : b.Ext c) : a.Ext c := by
  refine ⟨Nat.le_trans h1.1 h2.1, fun i blk h => ?_⟩
  obtain ⟨b1, hb1, hp1, E1, he1⟩ := h1.2 i blk h
  obtain ⟨b2, hb2, hp2, E2, he2⟩ := h2.2 i b1 hb1
  exact ⟨b2, hb2, hp2.trans hp1, E1 ++ E2, by rw [he2, he1, List.append_assoc]⟩

/-- What a fragment of the lowering may do to the builder's state: it grows the block table and the
value count; it leaves every existing block but the current one exactly as it was; and it ends with
no current block, the block it began in, or a block it created. -/
structure LS.Adv (ls ls' : LS) : Prop where
  ext : ls.Ext ls'
  vals : ls.vals.size ≤ ls'.vals.size
  keep : ∀ (i : Nat) (blk : BlockB), ls.cur ≠ some i → ls.blocks[i]? = some blk → ls'.blocks[i]? = some blk
  cur : ls'.cur = none ∨ ls'.cur = ls.cur ∨
    ∃ c, ls'.cur = some c ∧ ls.blocks.size ≤ c ∧ c < ls'.blocks.size
  stack : ls'.stack = ls.stack

theorem LS.Adv.refl (ls : LS) : ls.Adv ls :=
  ⟨.refl ls, Nat.le_refl _, fun _ _ _ h => h, Or.inr (Or.inl rfl), rfl⟩

theorem LS.Adv.trans {a b c : LS} (h1 : a.Adv b) (h2 : b.Adv c) : a.Adv c := by
  refine ⟨h1.ext.trans h2.ext, Nat.le_trans h1.vals h2.vals, fun i blk hne hb => ?_, ?_,
    h2.stack.trans h1.stack⟩
  · have hb1 := h1.keep i blk hne hb
    have hlt : i < a.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
    refine h2.keep i blk ?_ hb1
    rcases h1.cur with h | h | ⟨c, hc, hc1, _⟩
    · rw [h]; simp
    · rw [h]; exact hne
    · rw [hc]; intro hh; cases hh; omega
  · rcases h2.cur with h | h | ⟨c, hc, hc1, hc2⟩
    · exact Or.inl h
    · rw [h]
      rcases h1.cur with h' | h' | ⟨c', hc', hc1', hc2'⟩
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr ⟨c', hc', hc1', Nat.lt_of_lt_of_le hc2' h2.ext.1⟩)
    · exact Or.inr (Or.inr ⟨c, hc, Nat.le_trans h1.ext.1 hc1, hc2⟩)

/-! ### Primitive steps -/

/-- A change to one block that only appends instructions. -/
def Appends (F : BlockB → BlockB) : Prop :=
  ∀ blk, (F blk).params = blk.params ∧ ∃ E, (F blk).insts.toList = blk.insts.toList ++ E

theorem appends_push (i : Inst) : Appends (fun blk => { blk with insts := blk.insts.push i }) :=
  fun blk => ⟨rfl, [i], by simp⟩

theorem LS.Ext.modify {ls ls' : LS} (h : ls.Ext ls') {F : BlockB → BlockB} (hF : Appends F) (b : Nat) :
    ls.Ext { ls' with blocks := ls'.blocks.modify b F } := by
  refine ⟨by simpa using h.1, fun i blk hi => ?_⟩
  obtain ⟨b1, hb1, hp, E, he⟩ := h.2 i blk hi
  show ∃ blk' : BlockB, (ls'.blocks.modify b F)[i]? = some blk' ∧ _
  rw [Array.getElem?_modify, hb1]
  by_cases hbi : b = i
  · simp only [hbi, ↓reduceIte, Option.map_some]
    obtain ⟨hp2, E2, he2⟩ := hF b1
    exact ⟨F b1, rfl, hp2.trans hp, E ++ E2, by rw [he2, he, List.append_assoc]⟩
  · simp only [hbi, ↓reduceIte]
    exact ⟨b1, rfl, hp, E, he⟩

/-- Emitting into the current block, optionally defining a value and closing the block. -/
theorem LS.Adv.modCur {ls : LS} {b : BlockId} (hb : ls.cur = some b) {F : BlockB → BlockB}
    (hF : Appends F) {vs : Array (Option VTy)} (hv : ls.vals.size ≤ vs.size) {c : Option BlockId}
    (hc : c = ls.cur ∨ c = none) :
    ls.Adv { ls with blocks := ls.blocks.modify b F, vals := vs, cur := c } := by
  refine ⟨?_, hv, fun i blk hne hi => ?_, ?_, rfl⟩
  · have := (LS.Ext.refl ls).modify hF b
    exact this
  · have hbi : b ≠ i := fun h => hne (by rw [hb, h])
    show (ls.blocks.modify b F)[i]? = some blk
    rw [Array.getElem?_modify]
    simp [hbi, hi]
  · rcases hc with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h

theorem LS.Adv.newBlk (ls : LS) (blk : BlockB) {vs : Array (Option VTy)} (hv : ls.vals.size ≤ vs.size) :
    ls.Adv { ls with blocks := ls.blocks.push blk, vals := vs } := by
  refine ⟨⟨by simp, fun i b hi => ?_⟩, hv, fun i b _ hi => ?_, Or.inr (Or.inl rfl), rfl⟩
  · have hlt : i < ls.blocks.size := (Array.getElem?_eq_some_iff.mp hi).1
    refine ⟨b, ?_, rfl, [], by simp⟩
    show (ls.blocks.push blk)[i]? = some b
    rw [Array.getElem?_push]
    simp [Nat.ne_of_lt hlt, hi]
  · have hlt : i < ls.blocks.size := (Array.getElem?_eq_some_iff.mp hi).1
    show (ls.blocks.push blk)[i]? = some b
    rw [Array.getElem?_push]
    simp [Nat.ne_of_lt hlt, hi]

/-- Entering a block the fragment owns: the block it began in, or one created since. -/
theorem LS.Adv.setCur {ls0 ls1 : LS} (h : ls0.Adv ls1) {b : BlockId}
    (hb : some b = ls0.cur ∨ (ls0.blocks.size ≤ b ∧ b < ls1.blocks.size)) :
    ls0.Adv { ls1 with cur := some b } := by
  refine ⟨h.ext, h.vals, h.keep, ?_, h.stack⟩
  rcases hb with hb | ⟨hb1, hb2⟩
  · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr ⟨b, rfl, hb1, hb2⟩)

/-- Appending a terminator to an open block the fragment owns. -/
theorem LS.Adv.patch {ls0 ls1 : LS} (h : ls0.Adv ls1) (b : BlockId) (t : Term)
    (hb : some b = ls0.cur ∨ ls0.blocks.size ≤ b) :
    ls0.Adv { ls1 with
      blocks := ls1.blocks.modify b (fun blk => { blk with insts := blk.insts.push (.term t) }) } := by
  refine ⟨h.ext.modify (appends_push _) b, h.vals, fun i blk hne hi => ?_, ?_, h.stack⟩
  · have hlt : i < ls0.blocks.size := (Array.getElem?_eq_some_iff.mp hi).1
    have hbi : b ≠ i := by
      rintro rfl
      rcases hb with hb | hb
      · exact hne hb.symm
      · omega
    show (ls1.blocks.modify b _)[i]? = some blk
    rw [Array.getElem?_modify]
    simp [hbi, h.keep i blk hne hi]
  · rcases h.cur with hc | hc | ⟨c, hc, hc1, hc2⟩
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr ⟨c, hc, hc1, by simpa using hc2⟩)

theorem adv_emitDef {op : Op} {le : LEnv} {ls : LS} {r : ValueId} {ls' : LS}
    (h : emitDef op le ls = (r, ls')) : ls.Adv ls' := by
  cases hc : ls.cur with
  | none => rw [emitDef_none _ _ hc] at h; cases h; exact .refl ls
  | some b =>
    rw [emitDef_run _ _ hc] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h
    exact LS.Adv.modCur hc (appends_push _) (by simp) (Or.inl rfl)

theorem adv_emitEffect {e : Effect} {le : LEnv} {ls : LS} {r : Unit} {ls' : LS}
    (h : emitEffect e le ls = (r, ls')) : ls.Adv ls' := by
  cases hc : ls.cur with
  | none => rw [emitEffect_none _ _ hc] at h; cases h; exact .refl ls
  | some b =>
    rw [emitEffect_run _ _ hc] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h
    exact LS.Adv.modCur hc (appends_push _) (Nat.le_refl _) (Or.inl rfl)

theorem adv_emitTerm {t : Term} {le : LEnv} {ls : LS} {r : Unit} {ls' : LS}
    (h : emitTerm t le ls = (r, ls')) : ls.Adv ls' := by
  cases hc : ls.cur with
  | none => rw [emitTerm_none _ _ hc] at h; cases h; exact .refl ls
  | some b =>
    rw [emitTerm_run _ _ hc] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h
    exact LS.Adv.modCur hc (appends_push _) (Nat.le_refl _) (Or.inr rfl)

theorem adv_newBlock0 {le : LEnv} {ls : LS} {r ls'} (h : newBlock [] le ls = (r, ls')) : ls.Adv ls' := by
  rw [newBlock0_run] at h
  obtain ⟨-, rfl⟩ := Prod.mk.inj h
  exact LS.Adv.newBlk ls _ (Nat.le_refl _)

theorem adv_newBlock1 {t : VTy} {le : LEnv} {ls : LS} {r ls'} (h : newBlock [t] le ls = (r, ls')) :
    ls.Adv ls' := by
  rw [newBlock1_run] at h
  obtain ⟨-, rfl⟩ := Prod.mk.inj h
  exact LS.Adv.newBlk ls _ (by simp)

theorem adv_fork {cv : ValueId} {le : LEnv} {ls : LS} {b : BlockId} (hc : ls.cur = some b) {r ls'}
    (h : fork cv le ls = (r, ls')) : ls.Adv ls' := by
  rw [fork_run _ _ hc] at h
  obtain ⟨-, rfl⟩ := Prod.mk.inj h
  have h1 := LS.Adv.newBlk ls ⟨[], #[]⟩ (vs := ls.vals) (Nat.le_refl _)
  have h2 := LS.Adv.newBlk { ls with blocks := ls.blocks.push ⟨[], #[]⟩, vals := ls.vals } ⟨[], #[]⟩
    (vs := ls.vals) (Nat.le_refl _)
  have h3 := LS.Adv.modCur (ls := { ls with blocks := (ls.blocks.push ⟨[], #[]⟩).push ⟨[], #[]⟩ })
    (b := b) hc (appends_push (.term (.condbr cv ls.blocks.size [] (ls.blocks.size + 1) [])))
    (vs := ls.vals) (Nat.le_refl _) (c := none) (Or.inr rfl)
  exact h1.trans (h2.trans h3)

/-! ### Fragments -/

/-- The builder action `x` only advances the state as `LS.Adv` allows. -/
def AdvB (x : B α) : Prop := ∀ le ls r ls', x le ls = (r, ls') → ls.Adv ls'

theorem AdvB.pure (a : α) : AdvB (Pure.pure a : B α) := by
  intro le ls r ls' h
  rw [pure_run] at h
  obtain ⟨-, rfl⟩ := Prod.mk.inj h
  exact .refl _

theorem AdvB.bind {x : B α} {f : α → B β} (hx : AdvB x) (hf : ∀ a, AdvB (f a)) : AdvB (x >>= f) := by
  intro le ls r ls' h
  obtain ⟨a, ls1, h1, h2⟩ := bind_eq.mp h
  exact (hx _ _ _ _ h1).trans (hf a _ _ _ _ h2)

theorem advB_emitDef (op : Op) : AdvB (emitDef op) := fun _ _ _ _ h => adv_emitDef h
theorem advB_emitEffect (e : Effect) : AdvB (emitEffect e) := fun _ _ _ _ h => adv_emitEffect h
theorem advB_emitTerm (t : Term) : AdvB (emitTerm t) := fun _ _ _ _ h => adv_emitTerm h
theorem advB_newBlock0 : AdvB (newBlock []) := fun _ _ _ _ h => adv_newBlock0 h
theorem advB_newBlock1 (t : VTy) : AdvB (newBlock [t]) := fun _ _ _ _ h => adv_newBlock1 h

theorem inScope_eq {α : Type} {sc : ScopeId} {k : B α} {le : LEnv} {ls : LS} {r : α} {ls' : LS}
    (h : inScope sc k le ls = (r, ls')) :
    ∃ ls_k, k le { ls with stack := sc :: ls.stack } = (r, ls_k) ∧
      ls' = { ls_k with stack := ls_k.stack.drop 1 } := by
  unfold inScope at h
  simp only [bind_eq] at h
  obtain ⟨u1, ls1, h1, a, ls2, h2, u3, ls3, h3, hp⟩ := h
  rw [pushScope_run] at h1
  obtain ⟨-, rfl⟩ := Prod.mk.inj h1
  rw [pure_run] at hp
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
  rw [popScope_run] at h3
  obtain ⟨-, rfl⟩ := Prod.mk.inj h3
  exact ⟨ls2, h2, rfl⟩

theorem isLive_run {le : LEnv} {ls : LS} {b : BlockId} (h : ls.cur = some b) :
    isLive le ls = (true, ls) := by
  unfold isLive
  simp [bind_run, curBlock_run, pure_run, h]

theorem isLive_none {le : LEnv} {ls : LS} (h : ls.cur = none) : isLive le ls = (false, ls) := by
  unfold isLive
  simp [bind_run, curBlock_run, pure_run, h]

theorem advB_inScope {α : Type} (sc : ScopeId) {k : B α} (hk : AdvB k) : AdvB (inScope sc k) := by
  intro le ls r ls' h
  unfold inScope at h
  simp only [bind_eq] at h
  obtain ⟨u1, ls1, h1, a, ls2, h2, u3, ls3, h3, hp⟩ := h
  rw [pushScope_run] at h1
  obtain ⟨-, rfl⟩ := Prod.mk.inj h1
  rw [pure_run] at hp
  obtain ⟨-, rfl⟩ := Prod.mk.inj hp
  rw [popScope_run] at h3
  obtain ⟨-, rfl⟩ := Prod.mk.inj h3
  have a2 := hk _ _ _ _ h2
  exact ⟨a2.ext, a2.vals, a2.keep, a2.cur, by simp [a2.stack]⟩

theorem advB_curBlock : AdvB curBlock := by
  intro le ls r ls' h
  rw [curBlock_run] at h
  obtain ⟨-, rfl⟩ := Prod.mk.inj h
  exact .refl _

theorem advB_get : AdvB (get : B LS) := by
  intro le ls r ls' h
  obtain ⟨-, rfl⟩ := Prod.mk.inj h
  exact .refl _

theorem advB_read : AdvB (read : B LEnv) := by
  intro le ls r ls' h
  obtain ⟨-, rfl⟩ := Prod.mk.inj h
  exact .refl _

theorem valTy_run (v : ValueId) (le : LEnv) (ls : LS) : (valTy v le ls).2 = ls := by
  unfold valTy; simp [bind, pure]
  cases ls.vals[v]? with
  | none => rfl
  | some o => cases o <;> rfl

theorem advB_valTy (v : ValueId) : AdvB (valTy v) := by
  intro le ls r ls' h
  have := valTy_run v le ls
  rw [h] at this
  rw [← this]
  exact .refl _

theorem advB_intTyOf (v : ValueId) : AdvB (intTyOf v) := by
  unfold intTyOf
  refine AdvB.bind (advB_valTy v) fun t => ?_
  cases t with
  | data t => cases t <;> exact AdvB.pure _
  | view _ _ => exact AdvB.pure _

theorem advB_freezeTo (m : Mutability) (r : ValueId) : AdvB (freezeTo m r) := by
  unfold freezeTo
  refine AdvB.bind (advB_valTy r) fun t => ?_
  cases m <;> cases t <;> first
    | exact AdvB.pure _
    | (rename_i t; cases t <;> first | exact AdvB.pure _ | (rename_i m' _; cases m' <;> first | exact AdvB.pure _ | exact advB_emitDef _))

theorem advB_borrowTo (m : Mutability) (r : ValueId) : AdvB (borrowTo m r) := by
  unfold borrowTo
  refine AdvB.bind advB_read fun le => ?_
  refine AdvB.bind (advB_valTy r) fun t => ?_
  split <;> dsimp only <;> split <;> first | exact advB_emitDef _ | exact advB_freezeTo _ r

theorem advB_coerceTo (target : Ty) (r : ValueId) (org : OriginId) : AdvB (coerceTo target r org) := by
  unfold coerceTo
  refine AdvB.bind (advB_valTy r) fun source => ?_
  split
  · exact advB_emitDef _
  · exact AdvB.bind (advB_emitDef _) (fun _ => advB_emitDef _)
  · exact AdvB.pure _

theorem advB_coerceSlot (slot : SlotId) (value : ValueId) (org : OriginId) :
    AdvB (coerceSlot slot value org) := by
  unfold coerceSlot
  refine AdvB.bind advB_read fun le => ?_
  cases le.slots[slot]? with
  | none => exact AdvB.pure _
  | some destination => exact advB_coerceTo _ _ _

theorem advB_coerceResult (value : ValueId) (org : OriginId) :
    AdvB (coerceResult value org) := by
  unfold coerceResult
  refine AdvB.bind advB_read fun le => ?_
  cases le.results.head? with
  | none => exact AdvB.pure _
  | some destination => exact advB_coerceTo _ _ _

theorem advB_growOwner (r : ValueId) : AdvB (growOwner r) := by
  unfold growOwner
  refine AdvB.bind (advB_valTy r) fun t => ?_
  cases t with
  | data t => cases t <;> first | exact AdvB.pure _ | (rename_i m' t'; cases t' <;> exact AdvB.pure _)
  | view _ _ => exact AdvB.pure _

theorem advB_leaveAll : ∀ scs, AdvB (leaveAll scs)
  | [] => AdvB.pure _
  | sc :: rest => by
    unfold leaveAll
    exact AdvB.bind (advB_emitEffect _) fun _ => advB_leaveAll rest

theorem advB_leaveTo (d : Nat) : AdvB (leaveTo d) := by
  unfold leaveTo
  exact AdvB.bind advB_get fun _ => advB_leaveAll _

theorem advB_initSlots : ∀ ps, AdvB (initSlots ps)
  | [] => AdvB.pure _
  | (s, v, o) :: rest => by
    unfold initSlots
    exact AdvB.bind (advB_emitEffect _) fun _ => advB_initSlots rest

theorem advB_fork (cv : ValueId) : AdvB (fork cv) := by
  intro le ls r ls' h
  cases hc : ls.cur with
  | some b => exact adv_fork hc h
  | none =>
    unfold fork at h
    simp only [bind_run, newBlock0_run, pure_run] at h
    rw [emitTerm_none _ _ (by simpa using hc)] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h
    have h1 := LS.Adv.newBlk ls ⟨[], #[]⟩ (vs := ls.vals) (Nat.le_refl _)
    have h2 := LS.Adv.newBlk { ls with blocks := ls.blocks.push ⟨[], #[]⟩, vals := ls.vals } ⟨[], #[]⟩
      (vs := ls.vals) (Nat.le_refl _)
    exact h1.trans h2

theorem advB_whenLive (d : α) {k : BlockId → B α} (hk : ∀ b, AdvB (k b)) : AdvB (whenLive d k) := by
  intro le ls r ls' h
  cases hc : ls.cur with
  | none =>
    rw [whenLive_none _ _ _ hc] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h
    exact .refl _
  | some b =>
    rw [whenLive_some _ _ _ hc] at h
    exact hk b _ _ _ _ h

/-! ### Joins and short-circuit -/

/-- The block `b` is one a fragment that began in `ls0` may patch: the block it began in, or one
created since. -/
def Mine (ls0 : LS) (b : BlockId) : Prop := some b = ls0.cur ∨ ls0.blocks.size ≤ b

theorem LS.Adv.mine_cur {ls0 ls1 : LS} (h : ls0.Adv ls1) {b : BlockId} (hb : ls1.cur = some b) :
    Mine ls0 b := by
  rcases h.cur with hc | hc | ⟨c, hc, hc1, _⟩
  · rw [hb] at hc; cases hc
  · rw [hb] at hc; exact Or.inl hc
  · rw [hb] at hc; cases hc; exact Or.inr hc1

theorem adv_setCur_step {ls0 ls1 ls2 : LS} {b : BlockId} {u : Unit} {le : LEnv}
    (h : ls0.Adv ls1) (hb : Mine ls0 b) (hlt : b < ls1.blocks.size)
    (hs : setCur (some b) le ls1 = (u, ls2)) : ls0.Adv ls2 := by
  rw [setCur_run] at hs
  obtain ⟨-, rfl⟩ := Prod.mk.inj hs
  rcases hb with hb | hb
  · exact h.setCur (Or.inl hb)
  · exact h.setCur (Or.inr ⟨hb, hlt⟩)

theorem setCur_blocks {c : Option BlockId} {le : LEnv} {ls : LS} {u : Unit} {ls' : LS}
    (h : setCur c le ls = (u, ls')) : ls'.blocks = ls.blocks := by
  rw [setCur_run] at h
  obtain ⟨-, rfl⟩ := Prod.mk.inj h
  rfl

theorem curBlock_eq {le : LEnv} {ls : LS} {c : Option BlockId} {ls' : LS}
    (h : curBlock le ls = (c, ls')) : c = ls.cur ∧ ls' = ls := by
  rw [curBlock_run] at h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  exact ⟨h1.symm, h2.symm⟩

theorem adv_patch_step {ls0 ls1 ls2 : LS} {b : BlockId} {u : Unit} {le : LEnv} {t : Term}
    (h : ls0.Adv ls1) (hb : Mine ls0 b) (hs : patchTerm b t le ls1 = (u, ls2)) : ls0.Adv ls2 := by
  rw [patchTerm_run] at hs
  obtain ⟨-, rfl⟩ := Prod.mk.inj hs
  exact h.patch b t hb

theorem patchBrs_size {jb : BlockId} : ∀ (live : List (BlockId × ValueId)) {le : LEnv}
    {ls1 ls2 : LS} {u : Unit}, patchBrs jb live le ls1 = (u, ls2) → ls1.blocks.size = ls2.blocks.size
  | [], le, ls1, ls2, u, hp => by
    unfold patchBrs at hp
    rw [pure_run] at hp
    obtain ⟨-, rfl⟩ := Prod.mk.inj hp
    rfl
  | (b, v) :: rest, le, ls1, ls2, u, hp => by
    unfold patchBrs at hp
    obtain ⟨u1, ls3, h1, h2⟩ := bind_eq.mp hp
    rw [patchTerm_run] at h1
    obtain ⟨-, rfl⟩ := Prod.mk.inj h1
    have := patchBrs_size rest h2
    simpa using this

theorem patchBrs0_size {jb : BlockId} : ∀ (live : List BlockId) {le : LEnv}
    {ls1 ls2 : LS} {u : Unit}, patchBrs0 jb live le ls1 = (u, ls2) → ls1.blocks.size = ls2.blocks.size
  | [], le, ls1, ls2, u, hp => by
    unfold patchBrs0 at hp
    rw [pure_run] at hp
    obtain ⟨-, rfl⟩ := Prod.mk.inj hp
    rfl
  | b :: rest, le, ls1, ls2, u, hp => by
    unfold patchBrs0 at hp
    obtain ⟨u1, ls3, h1, h2⟩ := bind_eq.mp hp
    rw [patchTerm_run] at h1
    obtain ⟨-, rfl⟩ := Prod.mk.inj h1
    have := patchBrs0_size rest h2
    simpa using this

theorem adv_patchBrs {ls0 : LS} {jb : BlockId} : ∀ (live : List (BlockId × ValueId)) {le : LEnv}
    {ls1 ls2 : LS} {u : Unit}, ls0.Adv ls1 → (∀ p ∈ live, Mine ls0 p.1) →
    patchBrs jb live le ls1 = (u, ls2) → ls0.Adv ls2
  | [], le, ls1, ls2, u, h, _, hp => by
    unfold patchBrs at hp
    rw [pure_run] at hp
    obtain ⟨-, rfl⟩ := Prod.mk.inj hp
    exact h
  | (b, v) :: rest, le, ls1, ls2, u, h, hm, hp => by
    unfold patchBrs at hp
    obtain ⟨u1, ls3, h1, h2⟩ := bind_eq.mp hp
    have a1 := adv_patch_step h (hm (b, v) (by simp)) h1
    exact adv_patchBrs rest a1 (fun p hp => hm p (by simp [hp])) h2

theorem adv_patchBrs_ext {jb : BlockId} : ∀ (live : List (BlockId × ValueId)) {le : LEnv}
    {ls1 ls2 : LS} {u : Unit}, patchBrs jb live le ls1 = (u, ls2) → ls1.Ext ls2
  | [], le, ls1, ls2, u, hp => by
    unfold patchBrs at hp
    rw [pure_run] at hp
    obtain ⟨-, rfl⟩ := Prod.mk.inj hp
    exact LS.Ext.refl _
  | (b, v) :: rest, le, ls1, ls2, u, hp => by
    unfold patchBrs at hp
    obtain ⟨u1, ls3, h1, h2⟩ := bind_eq.mp hp
    rw [patchTerm_run] at h1
    obtain ⟨-, rfl⟩ := Prod.mk.inj h1
    exact ((LS.Ext.refl ls1).modify (appends_push _) b).trans (adv_patchBrs_ext rest h2)

theorem adv_patchBrs0_ext {jb : BlockId} : ∀ (live : List BlockId) {le : LEnv}
    {ls1 ls2 : LS} {u : Unit}, patchBrs0 jb live le ls1 = (u, ls2) → ls1.Ext ls2
  | [], le, ls1, ls2, u, hp => by
    unfold patchBrs0 at hp
    rw [pure_run] at hp
    obtain ⟨-, rfl⟩ := Prod.mk.inj hp
    exact LS.Ext.refl _
  | b :: rest, le, ls1, ls2, u, hp => by
    unfold patchBrs0 at hp
    obtain ⟨u1, ls3, h1, h2⟩ := bind_eq.mp hp
    rw [patchTerm_run] at h1
    obtain ⟨-, rfl⟩ := Prod.mk.inj h1
    exact ((LS.Ext.refl ls1).modify (appends_push _) b).trans (adv_patchBrs0_ext rest h2)

theorem adv_patchBrs0 {ls0 : LS} {jb : BlockId} : ∀ (live : List BlockId) {le : LEnv}
    {ls1 ls2 : LS} {u : Unit}, ls0.Adv ls1 → (∀ p ∈ live, Mine ls0 p) →
    patchBrs0 jb live le ls1 = (u, ls2) → ls0.Adv ls2
  | [], le, ls1, ls2, u, h, _, hp => by
    unfold patchBrs0 at hp
    rw [pure_run] at hp
    obtain ⟨-, rfl⟩ := Prod.mk.inj hp
    exact h
  | b :: rest, le, ls1, ls2, u, h, hm, hp => by
    unfold patchBrs0 at hp
    obtain ⟨u1, ls3, h1, h2⟩ := bind_eq.mp hp
    have a1 := adv_patch_step h (hm b (by simp)) h1
    exact adv_patchBrs0 rest a1 (fun p hp => hm p (by simp [hp])) h2

theorem valTy_eq {v : ValueId} {le : LEnv} {ls : LS} {t : VTy} {ls' : LS}
    (h : valTy v le ls = (t, ls')) : ls' = ls := by
  have := valTy_run v le ls
  rw [h] at this
  exact this

theorem intTyOf_eq {v : ValueId} {le : LEnv} {ls : LS} {t : IntTy} {ls' : LS}
    (h : intTyOf v le ls = (t, ls')) : ls' = ls := by
  unfold intTyOf at h
  simp only [bind_run] at h
  have := valTy_run v le ls
  cases hv : valTy v le ls with
  | mk a s1 =>
    rw [hv] at this h
    simp only at this h
    subst this
    cases a with
    | data t' => cases t' <;> exact (Prod.mk.inj h).2.symm
    | view _ _ => exact (Prod.mk.inj h).2.symm

theorem coerceTo_cases {target : Ty} {r : ValueId} {le : LEnv} {ls : LS}
    {r' : ValueId} {ls' : LS} {org : OriginId} (h : coerceTo target r org le ls = (r', ls')) :
    (r' = r ∧ ls' = ls) ∨
    (∃ elem, target = .ref .readOnly elem ∧ emitDef (.refFreeze r) le ls = (r', ls')) ∨
    (∃ elem view mid, target = .slice .readOnly elem ∧
      emitDef (.sliceView r) le ls = (view, mid) ∧
      emitDef (.viewSlice .readOnly view .omitted .omitted (some org)) le mid = (r', ls')) := by
  unfold coerceTo at h
  simp only [bind_run] at h
  have hs := valTy_run r le ls
  cases hv : valTy r le ls with
  | mk source same =>
    rw [hv] at hs h
    simp only at hs h
    subst hs
    split at h
    · exact Or.inr (Or.inl ⟨_, rfl, h⟩)
    · simp only [bind_eq] at h
      obtain ⟨view, mid, hview, hslice⟩ := h
      exact Or.inr (Or.inr ⟨_, view, mid, rfl, hview, hslice⟩)
    · rw [pure_run] at h
      obtain ⟨hr, hls⟩ := Prod.mk.inj h
      exact Or.inl ⟨hr.symm, hls.symm⟩

theorem freezeTo_cases {m : Mutability} {r : ValueId} {le : LEnv} {ls : LS} {r' : ValueId} {ls' : LS}
    (h : freezeTo m r le ls = (r', ls')) :
    (r' = r ∧ ls' = ls) ∨ emitDef (.refFreeze r) le ls = (r', ls') := by
  unfold freezeTo at h
  simp only [bind_run] at h
  have hs := valTy_run r le ls
  cases hv : valTy r le ls with
  | mk a s1 =>
    rw [hv] at hs h
    simp only at hs h
    subst hs
    rcases m with _ | _ <;> rcases a with t | ⟨_, _⟩ <;>
      (try rcases t with _ | _ | _ | _ | _ | _ | _ | ⟨m', _⟩ | _ | _ | _) <;>
      (try rcases m' with _ | _) <;>
      first
        | exact Or.inl ⟨(Prod.mk.inj h).1.symm, (Prod.mk.inj h).2.symm⟩
        | exact Or.inr h

theorem borrowTo_cases {m : Mutability} {r : ValueId} {le : LEnv} {ls : LS}
    {r' : ValueId} {ls' : LS} (h : borrowTo m r le ls = (r', ls')) :
    freezeTo m r le ls = (r', ls') ∨ emitDef (.ownerBorrow r) le ls = (r', ls') := by
  unfold borrowTo at h
  simp only [bind_run, read_apply] at h
  have hs := valTy_run r le ls
  cases hv : valTy r le ls with
  | mk ty same =>
    rw [hv] at hs h
    simp only at hs h
    subst hs
    let owner := match ty with
      | .data (.ref .mutable (.grow _)) | .data (.ref .mutable (.growshrink _)) => true
      | _ => false
    change (if (m == .mutable && le.mod.profile == .shrink && owner) = true then
      emitDef (.ownerBorrow r) else freezeTo m r) le same = (r', ls') at h
    by_cases borrow : (m == .mutable && le.mod.profile == .shrink && owner) = true
    · rw [if_pos borrow] at h
      exact Or.inr h
    · rw [if_neg borrow] at h
      exact Or.inl h

theorem adv_joinValue {ls0 ls1 : LS} (h : ls0.Adv ls1) {endT endF : Option BlockId} {vt vf : ValueId}
    (hT : ∀ b, endT = some b → Mine ls0 b) (hF : ∀ b, endF = some b → Mine ls0 b)
    {le : LEnv} {r : ValueId} {ls' : LS} (hj : joinValue endT vt endF vf le ls1 = (r, ls')) :
    ls0.Adv ls' := by
  unfold joinValue at hj
  have key : ∀ {live : List (BlockId × ValueId)}, (∀ p ∈ live, Mine ls0 p.1) →
      (do
        let ty ← valTy (live.headD (0, 0)).2
        let (jb, js) ← newBlock [ty]
        patchBrs jb live
        setCur (some jb)
        pure (js.headD 0) : B ValueId) le ls1 = (r, ls') → ls0.Adv ls' := by
    intro live hlive hk
    simp only [bind_eq] at hk
    obtain ⟨ty, ls2, h1, ⟨jb, js⟩, ls3, h2, u, ls4, h3, u2, ls5, h4, hk⟩ := hk
    have hls2 := valTy_eq h1
    subst hls2
    have a2 := h.trans (adv_newBlock1 h2)
    have e2 := h2
    rw [newBlock1_run] at e2
    obtain ⟨e2a, e2b⟩ := Prod.mk.inj e2
    obtain ⟨hjb, -⟩ := Prod.mk.inj e2a
    have a3 := adv_patchBrs live a2 hlive h3
    have hsz : ls2.blocks.size < ls4.blocks.size := by
      have h5 := patchBrs_size live h3
      have : ls3.blocks.size = ls2.blocks.size + 1 := by rw [← e2b]; simp
      omega
    have hm : Mine ls0 jb := Or.inr (by rw [← hjb]; exact h.ext.1)
    rw [pure_run] at hk
    obtain ⟨-, rfl⟩ := Prod.mk.inj hk
    exact adv_setCur_step a3 hm (by rw [← hjb]; exact hsz) h4
  cases endT <;> cases endF
  · simp only [bind_eq] at hj
    obtain ⟨u, ls2, h1, hj⟩ := hj
    rw [setCur_run] at h1
    obtain ⟨-, rfl⟩ := Prod.mk.inj h1
    rw [pure_run] at hj
    obtain ⟨-, rfl⟩ := Prod.mk.inj hj
    exact ⟨h.ext, h.vals, h.keep, Or.inl rfl, h.stack⟩
  · refine key (fun p hp => ?_) hj
    simp at hp; subst hp; exact hF _ rfl
  · refine key (fun p hp => ?_) hj
    simp at hp; subst hp; exact hT _ rfl
  · refine key (fun p hp => ?_) hj
    simp at hp
    rcases hp with rfl | rfl
    · exact hT _ rfl
    · exact hF _ rfl

theorem adv_joinArms {ls0 ls1 : LS} (h : ls0.Adv ls1) {endT endF : Option BlockId}
    (hT : ∀ b, endT = some b → Mine ls0 b) (hF : ∀ b, endF = some b → Mine ls0 b)
    {le : LEnv} {r : Unit} {ls' : LS} (hj : joinArms endT endF le ls1 = (r, ls')) : ls0.Adv ls' := by
  unfold joinArms at hj
  have key : ∀ {live : List BlockId}, (∀ p ∈ live, Mine ls0 p) →
      (do
        let (jb, _) ← newBlock []
        patchBrs0 jb live
        setCur (some jb) : B Unit) le ls1 = (r, ls') → ls0.Adv ls' := by
    intro live hlive hk
    simp only [bind_eq] at hk
    obtain ⟨⟨jb, js⟩, ls3, h2, u, ls4, h3, h4⟩ := hk
    have a2 := h.trans (adv_newBlock0 h2)
    have e2 := h2
    rw [newBlock0_run] at e2
    obtain ⟨e2a, e2b⟩ := Prod.mk.inj e2
    obtain ⟨hjb, -⟩ := Prod.mk.inj e2a
    have a3 := adv_patchBrs0 live a2 hlive h3
    have hsz : ls1.blocks.size < ls4.blocks.size := by
      have h5 := patchBrs0_size live h3
      have : ls3.blocks.size = ls1.blocks.size + 1 := by rw [← e2b]; simp
      omega
    have hm : Mine ls0 jb := Or.inr (by rw [← hjb]; exact h.ext.1)
    exact adv_setCur_step a3 hm (by rw [← hjb]; exact hsz) h4
  cases endT <;> cases endF
  · simp only [bind_eq] at hj
    rw [setCur_run] at hj
    obtain ⟨-, rfl⟩ := Prod.mk.inj hj
    exact ⟨h.ext, h.vals, h.keep, Or.inl rfl, h.stack⟩
  · refine key (fun p hp => ?_) hj
    simp at hp; subst hp; exact hF _ rfl
  · refine key (fun p hp => ?_) hj
    simp at hp; subst hp; exact hT _ rfl
  · refine key (fun p hp => ?_) hj
    simp at hp
    rcases hp with rfl | rfl
    · exact hT _ rfl
    · exact hF _ rfl

theorem adv_scFork {isAnd : Bool} {x : ValueId} {le : LEnv} {ls : LS} {b : BlockId}
    (hc : ls.cur = some b) {r ls'} (h : scFork isAnd x le ls = (r, ls')) : ls.Adv ls' := by
  rw [scFork_run _ _ _ hc] at h
  obtain ⟨-, rfl⟩ := Prod.mk.inj h
  have h1 := LS.Adv.newBlk ls ⟨[], #[]⟩ (vs := ls.vals) (Nat.le_refl _)
  have h2 := LS.Adv.newBlk { ls with blocks := ls.blocks.push ⟨[], #[]⟩, vals := ls.vals }
    ⟨[(ls.vals.size, .data .bool)], #[]⟩ (vs := ls.vals.push (some (.data .bool))) (by simp)
  have h3 := LS.Adv.modCur
    (ls := { ls with
      blocks := (ls.blocks.push ⟨[], #[]⟩).push ⟨[(ls.vals.size, .data .bool)], #[]⟩
      vals := ls.vals.push (some (.data .bool)) })
    (b := b) hc (appends_push (.term (scTerm isAnd x ls.blocks.size (ls.blocks.size + 1))))
    (vs := ls.vals.push (some (.data .bool))) (Nat.le_refl _) (c := none) (Or.inr rfl)
  exact h1.trans (h2.trans h3)

theorem scFork_ids {isAnd : Bool} {x : ValueId} {le : LEnv} {ls : LS} {r ls'}
    (h : scFork isAnd x le ls = (r, ls')) :
    r = (ls.blocks.size, ls.blocks.size + 1, ls.vals.size) ∧ ls'.blocks.size = ls.blocks.size + 2 := by
  cases hc : ls.cur with
  | some b =>
    rw [scFork_run _ _ _ hc] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simp
  | none =>
    unfold scFork at h
    cases isAnd <;>
    · simp only [bind_run, newBlock0_run, newBlock1_run, pure_run, ite_true, ite_false,
        Bool.false_eq_true, ↓reduceIte, if_true, if_false] at h
      rw [emitTerm_none _ _ (by simpa using hc)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      simp

theorem advB_scFork (isAnd : Bool) (x : ValueId) : AdvB (scFork isAnd x) := by
  intro le ls r ls' h
  cases hc : ls.cur with
  | some b => exact adv_scFork hc h
  | none =>
    unfold scFork at h
    cases isAnd <;>
    · simp only [bind_run, newBlock0_run, newBlock1_run, pure_run, ite_true, ite_false,
        Bool.false_eq_true, ↓reduceIte, if_true, if_false] at h
      rw [emitTerm_none _ _ (by simpa using hc)] at h
      obtain ⟨-, rfl⟩ := Prod.mk.inj h
      have h1 := LS.Adv.newBlk ls ⟨[], #[]⟩ (vs := ls.vals) (Nat.le_refl _)
      have h2 := LS.Adv.newBlk { ls with blocks := ls.blocks.push ⟨[], #[]⟩, vals := ls.vals }
        ⟨[(ls.vals.size, .data .bool)], #[]⟩ (vs := ls.vals.push (some (.data .bool))) (by simp)
      exact h1.trans h2

theorem advB_shortCircuit (isAnd : Bool) (x : ValueId) {rhs : B ValueId} (hr : AdvB rhs) :
    AdvB (shortCircuit isAnd x rhs) := by
  unfold shortCircuit
  refine advB_whenLive _ fun b => ?_
  intro le ls0 r ls' h
  simp only [bind_eq] at h
  obtain ⟨⟨rb, jb, p⟩, ls1, h1, u2, ls2, h2, y, ls3, h3, u4, ls4, h4, u5, ls5, h5, hp⟩ := h
  obtain ⟨hids, hsz⟩ := scFork_ids h1
  obtain ⟨hrb, hr2⟩ := Prod.mk.inj hids
  obtain ⟨hjb, hpp⟩ := Prod.mk.inj hr2
  subst hrb hjb hpp
  have a1 := advB_scFork _ _ _ _ _ _ h1
  have hm : Mine ls0 ls0.blocks.size := Or.inr (Nat.le_refl _)
  have hl : ls0.blocks.size < ls1.blocks.size := by omega
  have a2 := adv_setCur_step a1 hm hl h2
  have b2 := setCur_blocks h2
  have a3x := hr _ _ _ _ h3
  have a3 := a2.trans a3x
  have a4x := adv_emitTerm h4
  have a4 := a3.trans a4x
  have s3 : ls1.blocks.size ≤ ls3.blocks.size := by
    have := a3x.ext.1; rw [b2] at this; exact this
  have s4 : ls3.blocks.size ≤ ls4.blocks.size := a4x.ext.1
  have hm' : Mine ls0 (ls0.blocks.size + 1) := Or.inr (Nat.le_succ_of_le (Nat.le_refl _))
  have hl' : ls0.blocks.size + 1 < ls4.blocks.size := by omega
  rw [pure_run] at hp
  obtain ⟨-, rfl⟩ := Prod.mk.inj hp
  exact adv_setCur_step a4 hm' hl' h5

theorem fork_ids {cv : ValueId} {le : LEnv} {ls : LS} {r : BlockId × BlockId} {ls' : LS}
    (h : fork cv le ls = (r, ls')) :
    r = (ls.blocks.size, ls.blocks.size + 1) ∧ ls'.blocks.size = ls.blocks.size + 2 := by
  cases hc : ls.cur with
  | some b =>
    rw [fork_run _ _ hc] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simp
  | none =>
    unfold fork at h
    simp only [bind_run, newBlock0_run, pure_run] at h
    rw [emitTerm_none _ _ (by simpa using hc)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simp

theorem Mine.of_adv {ls0 ls2 : LS} (h : ls0.Adv ls2) {b : BlockId} (hb : Mine ls2 b) : Mine ls0 b := by
  rcases hb with hb | hb
  · exact h.mine_cur hb.symm
  · exact Or.inr (Nat.le_trans h.ext.1 hb)

/-- After a fork: the two new blocks belong to the fragment. -/
theorem adv_fork_step {ls0 ls1 ls2 : LS} {cv : ValueId} {le : LEnv} {tb eb : BlockId}
    (h : ls0.Adv ls1) (hf : fork cv le ls1 = ((tb, eb), ls2)) :
    ls0.Adv ls2 ∧ Mine ls0 tb ∧ Mine ls0 eb ∧ tb < ls2.blocks.size ∧ eb < ls2.blocks.size := by
  obtain ⟨hr, hs⟩ := fork_ids hf
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
  have := h.ext.1
  have h1 : ls1.blocks.size < ls2.blocks.size := by omega
  have h2 : ls1.blocks.size + 1 < ls2.blocks.size := by omega
  have h3 : ls0.blocks.size ≤ ls1.blocks.size + 1 := by omega
  exact ⟨h.trans (advB_fork _ _ _ _ _ hf), Or.inr this, Or.inr h3, h1, h2⟩

/-! ### Composite statements and expressions -/

theorem advB_isLive : AdvB isLive := by
  unfold isLive
  exact AdvB.bind advB_curBlock fun _ => AdvB.pure _

/-- Two arms, each started in a block of its own, joined to a block that takes the arms' values. -/
theorem advB_eachElemValue (x : VarId) (byRef : Bool) (elem : ValueId) :
    AdvB (eachElemValue x byRef elem) := by
  unfold eachElemValue
  cases byRef
  · exact advB_emitDef _
  · refine AdvB.bind advB_read fun le => ?_
    cases le.vars[x]? with
    | none => exact AdvB.pure _
    | some lv =>
      dsimp only
      cases lv.ty with
      | ref m t => exact advB_borrowTo m elem
      | _ => exact AdvB.pure _

theorem advB_ifE_core (cv : ValueId) {a1 a2 : B ValueId} (h1 : AdvB a1) (h2 : AdvB a2) :
    AdvB (whenLive 0 fun _ => do
      let (tb, eb) ← fork cv
      setCur (some tb)
      let vt ← a1
      let endT ← curBlock
      setCur (some eb)
      let vf ← a2
      let endF ← curBlock
      joinValue endT vt endF vf) := by
  refine advB_whenLive _ fun b => ?_
  intro le ls0 r ls' h
  simp only [bind_eq] at h
  obtain ⟨⟨tb, eb⟩, ls1, hf, u1, ls2, hs1, vt, ls3, ha1, endT, ls4, hc1, u2, ls5, hs2, vf, ls6, ha2,
    endF, ls7, hc2, hj⟩ := h
  obtain ⟨a1', mtb, meb, ltb, leb⟩ := adv_fork_step (.refl ls0) hf
  have a2' := adv_setCur_step a1' mtb ltb hs1
  have b2 := setCur_blocks hs1
  have a3x := h1 _ _ _ _ ha1
  have a3 := a2'.trans a3x
  obtain ⟨e4c, e4⟩ := curBlock_eq hc1
  subst e4
  have s3 : ls1.blocks.size ≤ ls4.blocks.size := by
    have := a3x.ext.1; rw [b2] at this; exact this
  have leb' : eb < ls4.blocks.size := Nat.lt_of_lt_of_le leb s3
  have a5 := adv_setCur_step a3 meb leb' hs2
  have b5 := setCur_blocks hs2
  have a6x := h2 _ _ _ _ ha2
  have a6 := a5.trans a6x
  obtain ⟨e7c, e7⟩ := curBlock_eq hc2
  subst e7
  have hT : ∀ b, endT = some b → Mine ls0 b := by
    intro b hb
    rw [e4c] at hb
    exact Mine.of_adv a2' (a3x.mine_cur hb)
  have hF : ∀ b, endF = some b → Mine ls0 b := by
    intro b hb
    rw [e7c] at hb
    exact Mine.of_adv a5 (a6x.mine_cur hb)
  exact adv_joinValue a6 hT hF hj

theorem advB_ifS_some_core (cv : ValueId) {a1 a2 : B ValueId} (h1 : AdvB a1) (h2 : AdvB a2) :
    AdvB (whenLive () fun _ => do
      let (tb, eb) ← fork cv
      setCur (some tb)
      let _ ← a1
      let endT ← curBlock
      setCur (some eb)
      let _ ← a2
      let endF ← curBlock
      joinArms endT endF) := by
  refine advB_whenLive _ fun b => ?_
  intro le ls0 r ls' h
  simp only [bind_eq] at h
  obtain ⟨⟨tb, eb⟩, ls1, hf, u1, ls2, hs1, vt, ls3, ha1, endT, ls4, hc1, u2, ls5, hs2, vf, ls6, ha2,
    endF, ls7, hc2, hj⟩ := h
  obtain ⟨a1', mtb, meb, ltb, leb⟩ := adv_fork_step (.refl ls0) hf
  have a2' := adv_setCur_step a1' mtb ltb hs1
  have b2 := setCur_blocks hs1
  have a3x := h1 _ _ _ _ ha1
  have a3 := a2'.trans a3x
  obtain ⟨e4c, e4⟩ := curBlock_eq hc1
  subst e4
  have s3 : ls1.blocks.size ≤ ls4.blocks.size := by
    have := a3x.ext.1; rw [b2] at this; exact this
  have leb' : eb < ls4.blocks.size := Nat.lt_of_lt_of_le leb s3
  have a5 := adv_setCur_step a3 meb leb' hs2
  have b5 := setCur_blocks hs2
  have a6x := h2 _ _ _ _ ha2
  have a6 := a5.trans a6x
  obtain ⟨e7c, e7⟩ := curBlock_eq hc2
  subst e7
  have hT : ∀ b, endT = some b → Mine ls0 b := by
    intro b hb
    rw [e4c] at hb
    exact Mine.of_adv a2' (a3x.mine_cur hb)
  have hF : ∀ b, endF = some b → Mine ls0 b := by
    intro b hb
    rw [e7c] at hb
    exact Mine.of_adv a5 (a6x.mine_cur hb)
  exact adv_joinArms a6 hT hF hj

theorem advB_ifS_none_core (cv : ValueId) {a1 : B ValueId} (h1 : AdvB a1) :
    AdvB (whenLive () fun _ => do
      let (tb, jb) ← fork cv
      setCur (some tb)
      let _ ← a1
      emitTerm (.br jb [])
      setCur (some jb)) := by
  refine advB_whenLive _ fun b => ?_
  intro le ls0 r ls' h
  simp only [bind_eq] at h
  obtain ⟨⟨tb, jb⟩, ls1, hf, u1, ls2, hs1, vt, ls3, ha1, u2, ls4, ht, hs2⟩ := h
  obtain ⟨a1', mtb, mjb, ltb, ljb⟩ := adv_fork_step (.refl ls0) hf
  have a2' := adv_setCur_step a1' mtb ltb hs1
  have b2 := setCur_blocks hs1
  have a3x := h1 _ _ _ _ ha1
  have a3 := a2'.trans a3x
  have a4x := adv_emitTerm ht
  have a4 := a3.trans a4x
  have s3 : ls1.blocks.size ≤ ls3.blocks.size := by
    have := a3x.ext.1; rw [b2] at this; exact this
  have s4 : ls3.blocks.size ≤ ls4.blocks.size := a4x.ext.1
  have ljb' : jb < ls4.blocks.size := Nat.lt_of_lt_of_le ljb (Nat.le_trans s3 s4)
  exact adv_setCur_step a4 mjb ljb' hs2

theorem advB_assert_core (cv : ValueId) (org : OriginId) :
    AdvB (whenLive () fun _ => do
      let (pb, fb) ← fork cv
      setCur (some fb)
      emitTerm (.abort .assert (some org))
      setCur (some pb)) := by
  refine advB_whenLive _ fun b => ?_
  intro le ls0 r ls' h
  simp only [bind_eq] at h
  obtain ⟨⟨pb, fb⟩, ls1, hf, u1, ls2, hs1, u2, ls3, ht, hs2⟩ := h
  obtain ⟨a1', mpb, mfb, lpb, lfb⟩ := adv_fork_step (.refl ls0) hf
  have a2' := adv_setCur_step a1' mfb lfb hs1
  have b2 := setCur_blocks hs1
  have a3x := adv_emitTerm ht
  have a3 := a2'.trans a3x
  have s3 : ls1.blocks.size ≤ ls3.blocks.size := by
    have := a3x.ext.1; rw [b2] at this; exact this
  have lpb' : pb < ls3.blocks.size := Nat.lt_of_lt_of_le lpb s3
  exact adv_setCur_step a3 mpb lpb' hs2

theorem advB_rangeBack (t : IntTy) (i : ValueId) (hb : BlockId) : AdvB (rangeBack t i hb) := by
  unfold rangeBack
  refine AdvB.bind advB_isLive fun live => ?_
  cases live
  · exact AdvB.pure _
  · exact AdvB.bind (advB_emitDef _) fun _ => advB_emitTerm _

/-- The branch of a loop, its body and its exit. -/
theorem advB_loopBody (cv : ValueId) {body : Nat → BlockId → B ValueId} {back : B Unit}
    (hbody : ∀ d xb, AdvB (body d xb)) (hback : AdvB back) : AdvB (loopBody cv body back) := by
  intro le ls0 r ls' h
  unfold loopBody at h
  simp only [bind_eq] at h
  obtain ⟨st, ls4, h4, ⟨bb, xb⟩, lsf, hf, u1, ls2, hs1, vb, ls3, ha1, u2, ls5, hb5, hs2⟩ := h
  have e4 : ls4 = ls0 := (Prod.mk.inj h4).2.symm
  subst e4
  obtain ⟨a1, mbb, mxb, lbb, lxb⟩ := adv_fork_step (.refl ls4) hf
  have a2 := adv_setCur_step a1 mbb lbb hs1
  have b2 := setCur_blocks hs1
  have a3x := hbody _ _ _ _ _ _ ha1
  have a3 := a2.trans a3x
  have a5x := hback _ _ _ _ hb5
  have a5 := a3.trans a5x
  have s3 : lsf.blocks.size ≤ ls3.blocks.size := by
    have := a3x.ext.1; rw [b2] at this; exact this
  have s5 : ls3.blocks.size ≤ ls5.blocks.size := a5x.ext.1
  have lxb' : xb < ls5.blocks.size := Nat.lt_of_lt_of_le lxb (Nat.le_trans s3 s5)
  exact adv_setCur_step a5 mxb lxb' hs2

theorem advB_regrowOf (o : Option ValueId) : AdvB (regrowOf o) := by
  cases o with
  | none => exact AdvB.pure _
  | some r => exact advB_growOwner r

theorem advB_eachSampled (regrow : Bool) (vw : ValueId) : AdvB (eachSampled regrow vw) := by
  unfold eachSampled
  cases regrow
  · exact advB_emitDef _
  · exact AdvB.pure _

theorem advB_eachLen (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    AdvB (eachLen regrow owner sampled) := by
  unfold eachLen
  cases regrow
  · exact AdvB.pure _
  · exact advB_emitDef _

theorem advB_lowerWhile (hb : BlockId) {cond : B ValueId} {body : Nat → BlockId → B ValueId}
    (hc : AdvB cond) (hbody : ∀ d xb, AdvB (body d xb)) : AdvB (lowerWhile hb cond body) := by
  unfold lowerWhile
  exact AdvB.bind hc fun cv => advB_whenLive _ fun _ =>
    advB_loopBody cv hbody (advB_emitTerm _)

theorem advB_lowerRange (t : IntTy) (i b : ValueId) (hb : BlockId) {body : Nat → BlockId → B ValueId}
    (hbody : ∀ d xb, AdvB (body d xb)) : AdvB (lowerRange t i b hb body) := by
  unfold lowerRange
  exact AdvB.bind (advB_emitDef _) fun c => advB_loopBody c hbody (advB_rangeBack _ _ _)

theorem advB_lowerEach (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) (hb : BlockId)
    (i : ValueId) {body : Nat → BlockId → B ValueId} (hbody : ∀ d xb, AdvB (body d xb)) :
    AdvB (lowerEach regrow owner sampled hb i body) := by
  unfold lowerEach
  exact AdvB.bind (advB_eachLen _ _ _) fun n => AdvB.bind (advB_emitDef _) fun c =>
    advB_loopBody c hbody (advB_rangeBack _ _ _)

/-- A loop header with no parameter: created, jumped to, and entered. -/
theorem advB_header0 {tail : BlockId → B Unit} (ht : ∀ h, AdvB (tail h)) :
    AdvB (do
      let (hb, _) ← newBlock []
      emitTerm (.br hb [])
      setCur (some hb)
      tail hb) := by
  intro le ls0 r ls' h
  simp only [bind_eq] at h
  obtain ⟨⟨hb', ps⟩, ls1, h1, u1, ls2, h2, u3, ls3, h3, ht'⟩ := h
  have e1 := h1
  rw [newBlock0_run] at e1
  obtain ⟨e1a, e1b⟩ := Prod.mk.inj e1
  obtain ⟨hh, -⟩ := Prod.mk.inj e1a
  have s1 : ls1.blocks.size = ls0.blocks.size + 1 := by rw [← e1b]; simp
  have a1 := adv_newBlock0 h1
  have a2 := a1.trans (adv_emitTerm h2)
  have s2 : ls1.blocks.size ≤ ls2.blocks.size := (adv_emitTerm h2).ext.1
  have hm : Mine ls0 hb' := Or.inr (by rw [← hh]; exact Nat.le_refl _)
  have hlt : hb' < ls2.blocks.size := by rw [← hh]; nat_omega
  have a3 := adv_setCur_step a2 hm hlt h3
  exact a3.trans (ht hb' _ _ _ _ ht')

/-- A loop header with one parameter, the first value of which is `a`. -/
theorem advB_header1 (ty : VTy) (a : ValueId) {tail : BlockId → ValueId → B Unit}
    (ht : ∀ h i, AdvB (tail h i)) :
    AdvB (do
      let (hb, hs) ← newBlock [ty]
      let i := hs.headD 0
      emitTerm (.br hb [a])
      setCur (some hb)
      tail hb i) := by
  intro le ls0 r ls' h
  simp only [bind_eq] at h
  obtain ⟨⟨hb', hs⟩, ls1, h1, u1, ls2, h2, u3, ls3, h3, ht'⟩ := h
  have e1 := h1
  rw [newBlock1_run] at e1
  obtain ⟨e1a, e1b⟩ := Prod.mk.inj e1
  obtain ⟨hh, -⟩ := Prod.mk.inj e1a
  have s1 : ls1.blocks.size = ls0.blocks.size + 1 := by rw [← e1b]; simp
  have a1 := adv_newBlock1 h1
  have a2 := a1.trans (adv_emitTerm h2)
  have s2 : ls1.blocks.size ≤ ls2.blocks.size := (adv_emitTerm h2).ext.1
  have hm : Mine ls0 hb' := Or.inr (by rw [← hh]; exact Nat.le_refl _)
  have hlt : hb' < ls2.blocks.size := by rw [← hh]; nat_omega
  have a3 := adv_setCur_step a2 hm hlt h3
  exact a3.trans (ht hb' _ _ _ _ _ ht')

/-! ### Every fragment of the lowering -/

mutual

theorem advB_lowerExpr : ∀ e : Expr, AdvB (lowerExpr e)
  | .structLit t es => by
    simp only [lowerExpr]
    exact AdvB.bind (advB_lowerExprs es) fun _ => advB_emitDef _
  | .lit t n => by simp only [lowerExpr]; exact advB_emitDef _
  | .bool b => by simp only [lowerExpr]; exact advB_emitDef _
  | .read p => by
    simp only [lowerExpr]
    exact AdvB.bind (advB_lowerPlace p) fun _ => advB_emitDef _
  | .ref m p => by
    simp only [lowerExpr]
    exact AdvB.bind (advB_lowerPlace p) fun r => advB_borrowTo m r
  | .slice m v lo hi org => by
    simp only [lowerExpr]
    exact AdvB.bind (advB_lowerView v) fun _ => AdvB.bind (advB_lowerBound lo) fun _ =>
      AdvB.bind (advB_lowerBound hi) fun _ => advB_emitDef _
  | .len v => by
    simp only [lowerExpr]
    exact AdvB.bind (advB_lowerView v) fun _ => advB_emitDef _
  | .un op e org => by
    simp only [lowerExpr]
    exact AdvB.bind (advB_lowerExpr e) fun a => AdvB.bind (advB_intTyOf a) fun _ => advB_emitDef _
  | .bin op a b org => by
    simp only [lowerExpr]
    exact AdvB.bind (advB_lowerExpr a) fun x => AdvB.bind (advB_lowerExpr b) fun y =>
      AdvB.bind (advB_intTyOf x) fun _ => advB_emitDef _
  | .cmp op a b => by
    simp only [lowerExpr]
    refine AdvB.bind (advB_lowerExpr a) fun x => AdvB.bind (advB_lowerExpr b) fun y =>
      AdvB.bind (advB_valTy x) fun t => ?_
    cases t with
    | data t => cases t <;> exact advB_emitDef _
    | view _ _ => exact advB_emitDef _
  | .and a b => by
    simp only [lowerExpr]
    exact AdvB.bind (advB_lowerExpr a) fun x => advB_shortCircuit true x (advB_lowerExpr b)
  | .or a b => by
    simp only [lowerExpr]
    exact AdvB.bind (advB_lowerExpr a) fun x => advB_shortCircuit false x (advB_lowerExpr b)
  | .not e => by
    simp only [lowerExpr]
    exact AdvB.bind (advB_lowerExpr e) fun _ => advB_emitDef _
  | .conv k target e org => by
    simp only [lowerExpr]
    exact AdvB.bind (advB_lowerExpr e) fun a => AdvB.bind (advB_intTyOf a) fun _ => advB_emitDef _
  | .call c args org => by
    simp only [lowerExpr]
    exact AdvB.bind (advB_lowerArgs args) fun _ => AdvB.bind (advB_emitDef _) fun r => AdvB.bind advB_read fun le => by
        cases hnr : le.mod.noReturn c <;> simp only [hnr, Bool.false_eq_true, ↓reduceIte] <;>
          first | exact AdvB.pure _ | exact AdvB.bind (advB_emitTerm _) fun _ => AdvB.pure _
  | .push owner e org => by
    simp only [lowerExpr]
    exact AdvB.bind (advB_lowerPlace owner) fun r => AdvB.bind (advB_lowerExpr e) fun v =>
      advB_emitDef (.push r v org)
  | .pop owner org => by
    simp only [lowerExpr]
    exact AdvB.bind (advB_lowerPlace owner) fun _ => advB_emitDef _
  | .ifE c t f => by
    simp only [lowerExpr]
    exact AdvB.bind (advB_lowerExpr c) fun cv =>
      advB_ifE_core cv (advB_lowerBlock none [] true t) (advB_lowerBlock none [] true f)
  | .blockE b => by
    simp only [lowerExpr]
    exact advB_lowerBlock none [] true b
  | .arrLit t es => by
    simp only [lowerExpr]
    exact AdvB.bind (advB_lowerExprs es) fun _ => advB_emitDef _
  | .fill t e => by
    simp only [lowerExpr]
    exact AdvB.bind (advB_lowerExpr e) fun _ => advB_emitDef _

theorem advB_lowerExprs : ∀ es : List Expr, AdvB (lowerExprs es)
  | [] => by simp only [lowerExprs]; exact AdvB.pure _
  | e :: rest => by
    simp only [lowerExprs]
    exact AdvB.bind (advB_lowerExpr e) fun _ => AdvB.bind (advB_lowerExprs rest) fun _ => AdvB.pure _

theorem advB_lowerArg : ∀ a : Arg, AdvB (lowerArg a)
  | .byVal e => by simp only [lowerArg]; exact advB_lowerExpr e
  | .byRef m p => by
    simp only [lowerArg]
    exact AdvB.bind (advB_lowerPlace p) fun r => advB_borrowTo m r

theorem advB_lowerArgs : ∀ as : List Arg, AdvB (lowerArgs as)
  | [] => by simp only [lowerArgs]; exact AdvB.pure _
  | a :: rest => by
    simp only [lowerArgs]
    exact AdvB.bind (advB_lowerArg a) fun _ => AdvB.bind (advB_lowerArgs rest) fun _ => AdvB.pure _

theorem advB_lowerPlace : ∀ p : Place, AdvB (lowerPlace p)
  | .field owner i => by
    simp only [lowerPlace]
    exact AdvB.bind (advB_lowerPlace owner) fun _ => advB_emitDef _
  | .var x => by simp only [lowerPlace]; exact advB_emitDef _
  | .global g => by simp only [lowerPlace]; exact advB_emitDef _
  | .deref e => by simp only [lowerPlace]; exact advB_lowerExpr e
  | .elem v i org => by
    simp only [lowerPlace]
    exact AdvB.bind (advB_lowerView v) fun _ => AdvB.bind (advB_lowerExpr i) fun _ => advB_emitDef _

theorem advB_lowerView : ∀ v : View, AdvB (lowerView v)
  | .of p => by
    simp only [lowerView]
    exact AdvB.bind (advB_lowerPlace p) fun _ => advB_emitDef _
  | .val e => by
    simp only [lowerView]
    exact AdvB.bind (advB_lowerExpr e) fun _ => advB_emitDef _

theorem advB_lowerBound : ∀ b : Bound, AdvB (lowerBound b)
  | .omitted => by simp only [lowerBound]; exact AdvB.pure _
  | .expr e => by
    simp only [lowerBound]
    exact AdvB.bind (advB_lowerExpr e) fun _ => AdvB.pure _
  | .fromEnd e => by
    simp only [lowerBound]
    exact AdvB.bind (advB_lowerExpr e) fun _ => AdvB.pure _

theorem advB_lowerEachSource : ∀ v : View, AdvB (lowerEachSource v)
  | .of p => by
    simp only [lowerEachSource]
    exact AdvB.bind (advB_lowerPlace p) fun _ => AdvB.bind (advB_emitDef _) fun _ => AdvB.pure _
  | .val e => by
    simp only [lowerEachSource]
    exact AdvB.bind (advB_lowerExpr e) fun _ => AdvB.bind (advB_emitDef _) fun _ => AdvB.pure _

theorem advB_lowerBlockValue (want : Bool) : ∀ v : Option Expr, AdvB (lowerBlockValue want v)
  | some e => by simp only [lowerBlockValue]; exact advB_lowerExpr e
  | none => by
    cases want
    · simp only [lowerBlockValue, Bool.false_eq_true, ↓reduceIte]; exact AdvB.pure _
    · simp only [lowerBlockValue, ↓reduceIte]; exact advB_emitDef _

theorem advB_lowerBlock (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ b : Block, AdvB (lowerBlock lc pre want b)
  | .mk sc stmts value => by
    simp only [lowerBlock]
    exact AdvB.bind (advB_emitEffect _) fun _ => advB_inScope sc
      (AdvB.bind (advB_initSlots _) fun _ => AdvB.bind (advB_lowerStmts lc stmts) fun _ =>
        AdvB.bind (advB_lowerBlockValue want value) fun _ => AdvB.bind (advB_emitEffect _) fun _ =>
        AdvB.pure _)

theorem advB_lowerStmts (lc : Option LoopCtx) : ∀ ss : List Stmt, AdvB (lowerStmts lc ss)
  | [] => by simp only [lowerStmts]; exact AdvB.pure _
  | s :: rest => by
    simp only [lowerStmts]
    refine AdvB.bind advB_isLive fun live => ?_
    cases live
    · exact AdvB.pure _
    · exact AdvB.bind (advB_lowerStmt lc s) fun _ => advB_lowerStmts lc rest

theorem advB_lowerPrintArgs : ∀ as : List PrintArg, AdvB (lowerPrintArgs as)
  | [] => by simp only [lowerPrintArgs]; exact AdvB.pure _
  | .text s :: rest => by
    simp only [lowerPrintArgs]
    exact AdvB.bind (advB_lowerPrintArgs rest) fun _ => AdvB.pure _
  | .expr e :: rest => by
    simp only [lowerPrintArgs]
    exact AdvB.bind (advB_lowerExpr e) fun _ => AdvB.bind (advB_lowerPrintArgs rest) fun _ => AdvB.pure _

theorem advB_lowerStmt (lc : Option LoopCtx) : ∀ s : Stmt, AdvB (lowerStmt lc s)
  | .letS x e org => by
    simp only [lowerStmt]
    exact AdvB.bind (advB_lowerExpr e) fun v =>
      AdvB.bind (advB_coerceSlot x v org) fun _ => advB_emitEffect _
  | .assign p e org => by
    simp only [lowerStmt]
    exact AdvB.bind (advB_lowerPlace p) fun _ => AdvB.bind (advB_lowerExpr e) fun _ => advB_emitEffect _
  | .assignOp op p e org => by
    simp only [lowerStmt]
    exact AdvB.bind (advB_lowerPlace p) fun _ => AdvB.bind (advB_emitDef _) fun _ =>
      AdvB.bind (advB_lowerExpr e) fun _ => AdvB.bind (advB_intTyOf _) fun _ =>
      AdvB.bind (advB_emitDef _) fun _ => advB_emitEffect _
  | .rebind x e org => by
    simp only [lowerStmt]
    exact AdvB.bind (advB_lowerExpr e) fun v =>
      AdvB.bind (advB_coerceSlot x v org) fun _ =>
        AdvB.bind (advB_emitDef _) fun _ => advB_emitEffect _
  | .expr e _ => by
    simp only [lowerStmt]
    exact AdvB.bind (advB_lowerExpr e) fun _ => AdvB.pure _
  | .append owner src org => by
    simp only [lowerStmt]
    exact AdvB.bind (advB_lowerPlace owner) fun _ => AdvB.bind (advB_lowerView src) fun _ =>
      advB_emitEffect _
  | .popN owner count org => by
    simp only [lowerStmt]
    exact AdvB.bind (advB_lowerPlace owner) fun r => AdvB.bind (advB_lowerExpr count) fun n =>
      advB_emitEffect (.popN r n (some org))
  | .resize owner size none org => by
    simp only [lowerStmt]
    exact AdvB.bind (advB_lowerPlace owner) fun r => AdvB.bind (advB_lowerExpr size) fun n =>
      AdvB.bind (AdvB.pure _) fun fill => advB_emitEffect (.resize r n fill (some org))
  | .resize owner size (some fill) org => by
    simp only [lowerStmt]
    exact AdvB.bind (advB_lowerPlace owner) fun r => AdvB.bind (advB_lowerExpr size) fun n =>
      AdvB.bind (advB_lowerExpr fill) fun v =>
        advB_emitEffect (.resize r n (some v) (some org))
  | .clear owner org => by
    simp only [lowerStmt]
    exact AdvB.bind (advB_lowerPlace owner) fun r => advB_emitEffect (.clear r (some org))
  | .assignWhole owner replacement org => by
    simp only [lowerStmt]
    exact AdvB.bind (advB_lowerPlace owner) fun r =>
      AdvB.bind (advB_emitEffect (.clear r (some org))) fun _ =>
      AdvB.bind (advB_lowerExpr replacement) fun run =>
        advB_emitEffect (.replace r run (some org))
  | .ifS c t f _ => by
    cases f with
    | none =>
      simp only [lowerStmt]
      exact AdvB.bind (advB_lowerExpr c) fun cv => advB_ifS_none_core cv (advB_lowerBlock lc [] false t)
    | some fb =>
      simp only [lowerStmt]
      exact AdvB.bind (advB_lowerExpr c) fun cv =>
        advB_ifS_some_core cv (advB_lowerBlock lc [] false t) (advB_lowerBlock lc [] false fb)
  | .while c body _ => by
    simp only [lowerStmt]
    exact advB_header0 (tail := fun hb => lowerWhile hb (lowerExpr c)
        (fun d xb => lowerBlock (some ⟨d, xb, .jump hb⟩) [] false body))
      (fun hb => advB_lowerWhile hb (advB_lowerExpr c) (fun d xb => advB_lowerBlock _ _ _ body))
  | .forRange x lo hi body org => by
    simp only [lowerStmt]
    refine AdvB.bind (advB_lowerExpr lo) fun a => AdvB.bind (advB_lowerExpr hi) fun b =>
      advB_whenLive _ fun _ => AdvB.bind (advB_intTyOf a) fun t => ?_
    exact advB_header1 (.data (.int t)) a (tail := fun hb i => lowerRange t i b hb (fun d xb =>
        lowerBlock (some ⟨d, xb, .next hb t i⟩) [(x, i, org)] false body))
      (fun hb i => advB_lowerRange t i b hb (fun d xb => advB_lowerBlock _ _ _ body))
  | .forEach x idx v byRef body org => by
    simp only [lowerStmt]
    refine AdvB.bind (advB_lowerEachSource v) fun ov => AdvB.bind (advB_regrowOf _) fun regrow =>
      AdvB.bind (advB_eachSampled _ _) fun sampled => AdvB.bind (advB_emitDef _) fun startAt =>
      advB_whenLive _ fun _ => ?_
    exact advB_header1 (.data (.int .i64)) startAt (tail := fun hb i =>
        lowerEach regrow ov.1 sampled hb i (fun d xb => do
          let elem ← emitDef (.refElem ov.2 i)
          let ev ← eachElemValue x byRef elem
          let pre := (x, ev, org) :: (match idx with
            | some j => [(j, i, org)]
            | none => [])
          lowerBlock (some ⟨d, xb, .next hb .i64 i⟩) pre false body))
      (fun hb i => advB_lowerEach regrow ov.1 sampled hb i (fun d xb =>
        AdvB.bind (advB_emitDef _) fun elem => AdvB.bind (advB_eachElemValue _ _ _) fun ev =>
          advB_lowerBlock _ _ _ body))
  | .ret e org => by
    cases e with
    | some e =>
      simp only [lowerStmt]
      exact AdvB.bind (advB_lowerExpr e) fun v => AdvB.bind (advB_coerceResult v org) fun _ =>
        AdvB.bind (AdvB.pure _) fun _ => AdvB.bind (advB_leaveTo 0) fun _ => advB_emitTerm _
    | none =>
      simp only [lowerStmt]
      exact AdvB.bind (AdvB.pure _) fun _ => AdvB.bind (advB_leaveTo 0) fun _ => advB_emitTerm _
  | .brk _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact AdvB.pure _
    | some l =>
      simp only [lowerStmt]
      exact AdvB.bind (advB_leaveTo _) fun _ => advB_emitTerm _
  | .cont _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact AdvB.pure _
    | some l =>
      cases hk : l.cont with
      | jump h =>
        simp only [lowerStmt, hk]
        exact AdvB.bind (advB_leaveTo _) fun _ => advB_emitTerm _
      | next h t i =>
        simp only [lowerStmt, hk]
        exact AdvB.bind (advB_leaveTo _) fun _ => AdvB.bind (advB_emitDef _) fun _ => advB_emitTerm _
  | .print args org => by
    simp only [lowerStmt]
    exact AdvB.bind (advB_lowerPrintArgs args) fun _ => advB_emitEffect _
  | .assertS e org => by
    simp only [lowerStmt]
    exact AdvB.bind (advB_lowerExpr e) fun cv => advB_assert_core cv org
  | .abort _ org => by
    simp only [lowerStmt]
    exact advB_emitTerm _
  | .exit e org => by
    simp only [lowerStmt]
    exact AdvB.bind (advB_lowerExpr e) fun _ => advB_emitTerm _

end

end Goose.Lower
