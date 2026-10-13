import Goose.Lower.Frag
import Goose.GIR.Validate

namespace Goose.Lower

open Goose.GIR (BlockId Effect Inst Op Term ValueId VTy)

def BlockB.defs (b : BlockB) : List ValueId :=
  b.params.map Prod.fst ++ b.insts.toList.filterMap fun
    | .def v _ => some v
    | _ => none

def LS.defs (ls : LS) : List ValueId :=
  ls.blocks.toList.flatMap BlockB.defs

def LS.insts (ls : LS) : List Inst :=
  ls.blocks.toList.flatMap fun blk => blk.insts.toList

def LS.appendInst (ls : LS) (b : BlockId) (i : Inst) : LS :=
  { ls with blocks := ls.blocks.modify b fun blk =>
    { blk with insts := blk.insts.push i } }

/-- Every emitted parameter or definition uses a distinct dense id. -/
def LS.DenseDefinitions (ls : LS) : Prop :=
  List.Perm ls.defs (List.range ls.vals.size)

/-- The index-bearing parts of an instruction are valid in the current builder tables. -/
def instSlotRefs : Inst → List Goose.GIR.SlotId
  | .def _ (.slotAddr s) | .eff (.slotInit s _ _) => [s]
  | _ => []

def instGlobalRefs : Inst → List Goose.Core.GlobalId
  | .def _ (.globalAddr g) => [g]
  | _ => []

def instFunctionRefs : Inst → List Goose.GIR.FnId
  | .def _ (.call f _ _) => [f]
  | _ => []

def instScopeRefs : Inst → List Goose.GIR.ScopeId
  | .eff (.enter sc) | .eff (.leave sc) => [sc]
  | _ => []

def instTargetRefs : Inst → List Goose.GIR.BlockId
  | .term t => t.successors
  | _ => []

def Op.SymbolRefsValid (le : LEnv) : Op → Prop
  | .slotAddr s => s < le.slots.size
  | .globalAddr g => g < le.globals.size
  | .call f _ _ => f < le.sigs.size
  | _ => True

def Effect.SymbolRefsValid (le : LEnv) (scopeCount : Nat) : Effect → Prop
  | .slotInit s _ _ => s < le.slots.size
  | .enter sc | .leave sc => sc < scopeCount
  | _ => True

/-! These are the GIR-V001 table-index facts for an instruction. They bound its SSA operands,
source-table references, origins, and successor blocks; they do not establish operation typing. -/
structure Inst.SymbolsWithin (le : LEnv) (scopeCount valueCount blockCount : Nat) (i : Inst) : Prop where
  uses : ∀ v ∈ i.uses, v < valueCount
  origin : ∀ o, i.origin = some o → o < le.mod.origins.size
  slots : ∀ s ∈ instSlotRefs i, s < le.slots.size
  globals : ∀ g ∈ instGlobalRefs i, g < le.globals.size
  functions : ∀ f ∈ instFunctionRefs i, f < le.sigs.size
  scopes : ∀ sc ∈ instScopeRefs i, sc < scopeCount
  targets : ∀ b ∈ instTargetRefs i, b < blockCount

theorem Inst.SymbolsWithin.def {le : LEnv} {scopeCount valueCount blockCount : Nat}
    {v : ValueId} {op : Op}
    (huses : ∀ x ∈ op.uses, x < valueCount)
    (horg : ∀ o, op.origin = some o → o < le.mod.origins.size)
    (hrefs : Op.SymbolRefsValid le op) :
    Inst.SymbolsWithin le scopeCount valueCount blockCount (.def v op) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Inst.uses] using huses
  · simpa [Inst.origin] using horg
  · intro s hs
    cases op <;> simp_all [instSlotRefs, Op.SymbolRefsValid]
  · intro g hg
    cases op <;> simp_all [instGlobalRefs, Op.SymbolRefsValid]
  · intro f hf
    cases op <;> simp_all [instFunctionRefs, Op.SymbolRefsValid]
  · simp [instScopeRefs]
  · simp [instTargetRefs]

theorem Inst.SymbolsWithin.eff {le : LEnv} {scopeCount valueCount blockCount : Nat}
    {e : Effect}
    (huses : ∀ x ∈ e.uses, x < valueCount)
    (horg : ∀ o, e.origin = some o → o < le.mod.origins.size)
    (hrefs : Effect.SymbolRefsValid le scopeCount e) :
    Inst.SymbolsWithin le scopeCount valueCount blockCount (.eff e) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Inst.uses] using huses
  · simpa [Inst.origin] using horg
  · intro s hs
    cases e <;> simp_all [instSlotRefs, Effect.SymbolRefsValid]
  · simp [instGlobalRefs]
  · simp [instFunctionRefs]
  · intro sc hsc
    cases e <;> simp_all [instScopeRefs, Effect.SymbolRefsValid]
  · simp [instTargetRefs]

theorem Inst.SymbolsWithin.term {le : LEnv} {scopeCount valueCount blockCount : Nat}
    {t : Term}
    (huses : ∀ x ∈ t.uses, x < valueCount)
    (horg : ∀ o, t.origin = some o → o < le.mod.origins.size)
    (htargets : ∀ b ∈ t.successors, b < blockCount) :
    Inst.SymbolsWithin le scopeCount valueCount blockCount (.term t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Inst.uses] using huses
  · simpa [Inst.origin] using horg
  · simp [instSlotRefs]
  · simp [instGlobalRefs]
  · simp [instFunctionRefs]
  · simp [instScopeRefs]
  · simpa [instTargetRefs] using htargets

/-! The lowering state satisfies the GIR-V001 table-index invariant: definitions are dense, and
every instruction reference names an entry in its corresponding table. This is not a type invariant. -/
structure LS.SymbolWF (le : LEnv) (scopeCount : Nat) (ls : LS) : Prop where
  definitions : ls.DenseDefinitions
  instructions : ∀ i ∈ ls.insts, Inst.SymbolsWithin le scopeCount ls.vals.size ls.blocks.size i

/-- A fragment preserves SymbolWF, never revives a closed path, and bounds every value it returns
when its result remains live. -/
def LS.CurrentBlocks (ls : LS) : Prop :=
  ∀ b, ls.cur = some b → b < ls.blocks.size

def LS.SymbolRun (le : LEnv) (scopeCount : Nat) (ls : LS)
    (ids : α → List ValueId) (action : B α) : Prop :=
  LS.SymbolWF le scopeCount ls → LS.CurrentBlocks ls → ∀ a ls',
    action le ls = (a, ls') →
    LS.SymbolWF le scopeCount ls' ∧
    LS.CurrentBlocks ls' ∧
    (ls.cur = none → ls'.cur = none) ∧
    (ls'.cur.isSome → ∀ v ∈ ids a, v < ls'.vals.size)

/-- A reference captured from a lowering result names one of the builder's
tables. Keeping the table in the constructor prevents a block id from being
mistaken for a value id. -/
inductive SymbolRef where
  | value (id : ValueId)
  | block (id : BlockId)
  | function (id : Goose.GIR.FnId)
  deriving DecidableEq, Repr

/-- A captured reference is checked against the exact builder state at which it
will be used. -/
def SymbolRef.Bound (le : LEnv) (ls : LS) : SymbolRef → Prop
  | .value v => v < ls.vals.size
  | .block b => b < ls.blocks.size
  | .function f => f < le.sigs.size

/-- Value results are available only when lowering left a live path. In
particular, the dummy value returned by `emitDef` on a closed path is not a
reference that a later lowering step may use. -/
def LS.valueRefs (ids : α → List ValueId) : α → LS → List SymbolRef :=
  fun a ls => if ls.cur.isSome then (ids a).map SymbolRef.value else []

/-- One builder action together with its exact output state. Result references
are checked in that state, after the action has finished. -/
def LS.SymbolRunAt (le : LEnv) (scopeCount : Nat) (ls : LS)
    (refs : α → LS → List SymbolRef) (action : B α) : Prop :=
  LS.SymbolWF le scopeCount ls → LS.CurrentBlocks ls → ∀ a ls',
    action le ls = (a, ls') →
    ls.Adv ls' ∧
    LS.SymbolWF le scopeCount ls' ∧
    LS.CurrentBlocks ls' ∧
    (ls.cur = none → ls'.cur = none) ∧
    (∀ r ∈ refs a ls', SymbolRef.Bound le ls' r)

theorem LS.SymbolRun.bind {le : LEnv} {scopeCount : Nat} {α β : Type}
    {ls : LS} {ids₁ : α → List ValueId} {ids₂ : β → List ValueId} {x : B α} {f : α → B β}
    (hx : LS.SymbolRun le scopeCount ls ids₁ x)
    (hf : ∀ a ls, LS.SymbolWF le scopeCount ls → LS.CurrentBlocks ls →
      (ls.cur.isSome → ∀ v ∈ ids₁ a, v < ls.vals.size) →
      LS.SymbolRun le scopeCount ls ids₂ (f a)) :
    LS.SymbolRun le scopeCount ls ids₂ (x >>= f) := by
  intro hls hc b ls' hrun
  obtain ⟨a, ls1, hxrun, hfrun⟩ := bind_eq.mp hrun
  obtain ⟨hls1, hc1, hdead1, hids1⟩ := hx hls hc a ls1 hxrun
  obtain ⟨hls2, hc2, hdead2, hids2⟩ :=
    hf a ls1 hls1 hc1 hids1 hls1 hc1 b ls' hfrun
  exact ⟨hls2, hc2, fun hdead => hdead2 (hdead1 hdead), hids2⟩

theorem LS.SymbolRun.stable {le : LEnv} {scopeCount : Nat} {ls : LS}
    {α : Type} {action : B α} (hstable : ∃ a, action le ls = (a, ls)) :
    LS.SymbolRun le scopeCount ls (fun _ : α => []) action := by
  intro hls hc a ls' hrun
  obtain ⟨a0, ha0⟩ := hstable
  rw [ha0] at hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
  exact ⟨hls, hc, fun h => h, by simp⟩

/-- Upgrade the value-only relation with exact state advancement. This bridge is
useful for existing value-producing fragments while new control-flow helpers
can state block and function references directly. -/
theorem LS.SymbolRun.toSymbolRunAt {le : LEnv} {scopeCount : Nat} {ls : LS}
    {α : Type} {ids : α → List ValueId} {action : B α}
    (h : LS.SymbolRun le scopeCount ls ids action) (ha : AdvB action) :
    LS.SymbolRunAt le scopeCount ls (LS.valueRefs ids) action := by
  intro hls hc a ls' hrun
  obtain ⟨hls', hc', hdead, hids⟩ := h hls hc a ls' hrun
  refine ⟨ha _ _ _ _ hrun, hls', hc', hdead, ?_⟩
  intro r hr
  by_cases hlive : ls'.cur.isSome
  · simp [LS.valueRefs, hlive] at hr
    obtain ⟨v, hv, hr⟩ := hr
    cases hr
    exact hids hlive v hv
  · simp [LS.valueRefs, hlive] at hr

/-- Bind composes exact states and gives the continuation the references
captured from the first action at its actual intermediate state. -/
theorem LS.SymbolRunAt.bind {le : LEnv} {scopeCount : Nat} {α β : Type}
    {ls : LS} {refs₁ : α → LS → List SymbolRef} {refs₂ : β → LS → List SymbolRef}
    {x : B α} {f : α → B β}
    (hx : LS.SymbolRunAt le scopeCount ls refs₁ x)
    (hf : ∀ a mid, LS.SymbolWF le scopeCount mid → LS.CurrentBlocks mid →
      (∀ r ∈ refs₁ a mid, SymbolRef.Bound le mid r) →
      ls.Adv mid → (ls.cur = none → mid.cur = none) →
      LS.SymbolRunAt le scopeCount mid refs₂ (f a)) :
    LS.SymbolRunAt le scopeCount ls refs₂ (x >>= f) := by
  intro hls hc b ls' hrun
  obtain ⟨a, ls1, hxrun, hfrun⟩ := bind_eq.mp hrun
  obtain ⟨hadv1, hls1, hc1, hdead1, hrefs1⟩ := hx hls hc a ls1 hxrun
  have hcontinue := hf a ls1 hls1 hc1 hrefs1 hadv1 hdead1
  obtain ⟨hadv2, hls2, hc2, hdead2, hrefs2⟩ := hcontinue hls1 hc1 b ls' hfrun
  exact ⟨hadv1.trans hadv2, hls2, hc2,
    fun hdead => hdead2 (hdead1 hdead), hrefs2⟩

theorem LS.SymbolRunAt.stable {le : LEnv} {scopeCount : Nat} {ls : LS}
    {α : Type} {refs : α → LS → List SymbolRef} {action : B α}
    (hstable : ∃ a, action le ls = (a, ls))
    (hrefs : ∀ a, action le ls = (a, ls) →
      ∀ r ∈ refs a ls, SymbolRef.Bound le ls r) :
    LS.SymbolRunAt le scopeCount ls refs action := by
  intro hls hc a ls' hrun
  obtain ⟨a0, ha0⟩ := hstable
  rw [ha0] at hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
  exact ⟨LS.Adv.refl _, hls, hc, fun h => h, hrefs a0 ha0⟩

theorem LS.SymbolRunAt.toSymbolRun {le : LEnv} {scopeCount : Nat} {ls : LS}
    {α : Type} {ids : α → List ValueId} {action : B α}
    (h : LS.SymbolRunAt le scopeCount ls (LS.valueRefs ids) action) :
    LS.SymbolRun le scopeCount ls ids action := by
  intro hls hc a ls' hrun
  obtain ⟨_, hls', hc', hdead, hrefs⟩ := h hls hc a ls' hrun
  refine ⟨hls', hc', hdead, ?_⟩
  intro hlive v hv
  have hmem : SymbolRef.value v ∈ LS.valueRefs ids a ls' := by
    simp [LS.valueRefs, hlive, hv]
  have hbound := hrefs (.value v) hmem
  exact hbound

theorem intTyOf_state (v : ValueId) (le : LEnv) (ls : LS) :
    (intTyOf v le ls).2 = ls := by
  unfold intTyOf
  rw [bind_run]
  cases hval : valTy v le ls with
  | mk ty ls' =>
    have hstate : ls' = ls := by simpa [hval] using valTy_run v le ls
    subst ls'
    cases ty with
    | data t => cases t <;> rfl
    | view _ _ => rfl

theorem LS.SymbolWF.changeCur {le : LEnv} {scopeCount : Nat} {ls : LS}
    (h : LS.SymbolWF le scopeCount ls) (cur : Option BlockId) :
    LS.SymbolWF le scopeCount { ls with cur := cur } := by
  cases h with
  | mk hd hi =>
    refine ⟨?_, ?_⟩
    · simpa [LS.DenseDefinitions, LS.defs] using hd
    · simpa [LS.insts] using hi

theorem Inst.SymbolsWithin.mono {le : LEnv} {scopeCount v₁ v₂ b₁ b₂ : Nat} {i : Inst}
    (h : Inst.SymbolsWithin le scopeCount v₁ b₁ i) (hv : v₁ ≤ v₂) (hb : b₁ ≤ b₂) :
    Inst.SymbolsWithin le scopeCount v₂ b₂ i := by
  refine ⟨?_, h.origin, h.slots, h.globals, h.functions, h.scopes, ?_⟩
  · intro v hv'
    exact Nat.lt_of_lt_of_le (h.uses v hv') hv
  · intro b hb'
    exact Nat.lt_of_lt_of_le (h.targets b hb') hb

theorem LS.DenseDefinitions.nodup {ls : LS} (h : ls.DenseDefinitions) : ls.defs.Nodup := by
  exact h.symm.nodup List.nodup_range

theorem LS.DenseDefinitions.length {ls : LS} (h : ls.DenseDefinitions) :
    ls.defs.length = ls.vals.size := by
  have := h.length_eq
  simpa using this

theorem LS.DenseDefinitions.mem_lt {ls : LS} (h : ls.DenseDefinitions) {v : ValueId}
    (hv : v ∈ ls.defs) : v < ls.vals.size := by
  have hrange : v ∈ List.range ls.vals.size := h.subset hv
  exact List.mem_range.mp hrange

def pushParamTypes (tys : List VTy) (vals : Array (Option VTy)) : Array (Option VTy) :=
  tys.foldl (fun a t => a.push (some t)) vals

def paramIds (tys : List VTy) (vals : Array (Option VTy)) : List ValueId :=
  (List.range tys.length).map (vals.size + ·)

theorem array_size_pushParamTypes (tys : List VTy) (vals : Array (Option VTy)) :
    (pushParamTypes tys vals).size = vals.size + tys.length := by
  induction tys generalizing vals with
  | nil => simp [pushParamTypes]
  | cons ty tys ih =>
    change (pushParamTypes tys (vals.push (some ty))).size = vals.size + (ty :: tys).length
    rw [ih (vals.push (some ty))]
    simp
    omega

private theorem map_fst_zip_self {α β : Type} (xs : List α) (ys : List β)
    (hlen : xs.length = ys.length) : (xs.zip ys).map Prod.fst = xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.zip_cons_cons, List.map_cons, Prod.fst]
      have htail : xs.length = ys.length := by simpa using hlen
      exact congrArg (List.cons x) (ih ys htail)

theorem newBlock_run_general (tys : List VTy) (le : LEnv) (ls : LS) :
    newBlock tys le ls =
      ((ls.blocks.size, paramIds tys ls.vals),
        { ls with
          blocks := ls.blocks.push ⟨(paramIds tys ls.vals).zip tys, #[]⟩
          vals := pushParamTypes tys ls.vals }) := by
  rfl

theorem LS.DenseDefinitions.newBlock {tys : List VTy} {le : LEnv} {ls : LS}
    (h : ls.DenseDefinitions) :
    ({ ls with
      blocks := ls.blocks.push ⟨(paramIds tys ls.vals).zip tys, #[]⟩
      vals := pushParamTypes tys ls.vals }).DenseDefinitions := by
  have hids : ((paramIds tys ls.vals).zip tys).map Prod.fst = paramIds tys ls.vals :=
    map_fst_zip_self _ _ (by simp [paramIds])
  have hdefs :
      ({ ls with
        blocks := ls.blocks.push ⟨(paramIds tys ls.vals).zip tys, #[]⟩
        vals := pushParamTypes tys ls.vals }).defs =
      ls.defs ++ paramIds tys ls.vals := by
    simp [LS.defs, BlockB.defs, hids]
  rw [LS.DenseDefinitions, hdefs, array_size_pushParamTypes]
  have hperm := h.append_right (paramIds tys ls.vals)
  have hrange :
      List.range ls.vals.size ++ paramIds tys ls.vals =
        List.range (ls.vals.size + tys.length) := by
    simp [paramIds, List.range_add]
  rw [hrange] at hperm
  exact hperm

theorem LS.SymbolWF.newBlock {tys : List VTy} {le : LEnv} {scopeCount : Nat} {ls : LS}
    (h : LS.SymbolWF le scopeCount ls) :
    LS.SymbolWF le scopeCount
      { ls with
        blocks := ls.blocks.push ⟨(paramIds tys ls.vals).zip tys, #[]⟩
        vals := pushParamTypes tys ls.vals } := by
  let ls' : LS := { ls with
    blocks := ls.blocks.push ⟨(paramIds tys ls.vals).zip tys, #[]⟩
    vals := pushParamTypes tys ls.vals }
  have hdefs := LS.DenseDefinitions.newBlock (tys := tys) (le := le) h.definitions
  have hvals : ls.vals.size ≤ ls'.vals.size := by simp [ls', array_size_pushParamTypes]
  have hblocks : ls.blocks.size ≤ ls'.blocks.size := by simp [ls']
  have hin : ls'.insts = ls.insts := by simp [LS.insts, ls']
  change LS.SymbolWF le scopeCount ls'
  refine ⟨?_, ?_⟩
  · simpa [LS.DenseDefinitions, LS.defs, ls'] using hdefs
  · intro i hi
    have hi' : i ∈ ls.insts := by simpa [hin] using hi
    exact (h.instructions i hi').mono hvals hblocks

theorem LS.SymbolWF.newBlockCur {tys : List VTy} {le : LEnv} {scopeCount : Nat} {ls : LS}
    (h : LS.SymbolWF le scopeCount ls) :
    LS.SymbolWF le scopeCount
      { (Goose.Lower.newBlock tys le ls).2 with
        cur := some (Goose.Lower.newBlock tys le ls).1.1 } := by
  rw [newBlock_run_general]
  exact h.newBlock.changeCur _

private theorem flatMap_modify_push {α β : Type} (f : α → List β) (xs : List α) (i : Nat)
    (g : α → α) (v : β) (hi : i < xs.length)
    (hupdate : ∀ x, f (g x) = f x ++ [v]) :
    List.Perm ((xs.modify i g).flatMap f) (xs.flatMap f ++ [v]) := by
  induction i generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at hi
    | cons x xs =>
      have hx := hupdate x
      have hswap : List.Perm ([v] ++ xs.flatMap f) (xs.flatMap f ++ [v]) :=
        List.perm_append_comm
      simp only [List.modify_zero_cons, List.flatMap_cons, hx]
      simpa [List.append_assoc] using List.Perm.append_left (f x) hswap
  | succ i ih =>
    cases xs with
    | nil => simp at hi
    | cons x xs =>
      have hi' : i < xs.length := by simpa using hi
      have htail := ih xs hi'
      simp only [List.modify_succ_cons, List.flatMap_cons]
      simpa [List.append_assoc] using List.Perm.append_left (f x) htail

private theorem flatMap_modifyAt_push {α β : Type} (f : α → List β) (xs : List α) (i : Nat)
    (g : α → α) (v : β) (hi : i < xs.length)
    (hg : f (g xs[i]) = f xs[i] ++ [v]) :
    List.Perm ((xs.modify i g).flatMap f) (xs.flatMap f ++ [v]) := by
  induction i generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at hi
    | cons x xs =>
      have hx : f (g x) = f x ++ [v] := by simpa using hg
      have hswap : List.Perm ([v] ++ xs.flatMap f) (xs.flatMap f ++ [v]) :=
        List.perm_append_comm
      simp only [List.modify_zero_cons, List.flatMap_cons, hx]
      simpa [List.append_assoc] using List.Perm.append_left (f x) hswap
  | succ i ih =>
    cases xs with
    | nil => simp at hi
    | cons x xs =>
      have hi' : i < xs.length := by simpa using hi
      have hg' : f (g xs[i]) = f xs[i] ++ [v] := by simpa using hg
      have htail := ih xs hi' hg'
      simp only [List.modify_succ_cons, List.flatMap_cons]
      simpa [List.append_assoc] using List.Perm.append_left (f x) htail

private theorem flatMap_modify_eq {α β : Type} (f : α → List β) (xs : List α) (i : Nat)
    (g : α → α) (hi : i < xs.length) (hupdate : ∀ x, f (g x) = f x) :
    (xs.modify i g).flatMap f = xs.flatMap f := by
  induction i generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at hi
    | cons x xs => simp [hupdate]
  | succ i ih =>
    cases xs with
    | nil => simp at hi
    | cons x xs =>
      have hi' : i < xs.length := by simpa using hi
      simp only [List.modify_succ_cons, List.flatMap_cons]
      rw [ih xs hi']

private theorem LS.DenseDefinitions.modifyNoNewDefs {ls : LS} {b : BlockId}
    (h : ls.DenseDefinitions) (hb : b < ls.blocks.size) (F : BlockB → BlockB)
    (hF : ∀ blk, BlockB.defs (F blk) = BlockB.defs blk) :
    ({ ls with blocks := ls.blocks.modify b F }).DenseDefinitions := by
  have heq : ({ ls with blocks := ls.blocks.modify b F }).defs = ls.defs := by
    simp only [LS.defs, Array.toList_modify]
    apply flatMap_modify_eq BlockB.defs ls.blocks.toList b F (by simpa using hb)
    exact hF
  rw [LS.DenseDefinitions, heq]
  exact h

private theorem LS.insts.modifyPush {ls : LS} {b : BlockId} (hb : b < ls.blocks.size)
    (i : Inst) :
    List.Perm
      ({ ls with blocks := ls.blocks.modify b fun blk =>
        { blk with insts := blk.insts.push i } }).insts
      (ls.insts ++ [i]) := by
  let xs := ls.blocks.toList
  let add := fun (blk : BlockB) => { blk with insts := blk.insts.push i }
  have hi : b < xs.length := by simpa [xs] using hb
  have hupdate : (add (xs[b]'hi)).insts.toList =
      (xs[b]'hi).insts.toList ++ [i] := by
    simp [add]
  have hperm := flatMap_modifyAt_push (fun blk : BlockB => blk.insts.toList)
    xs b add i hi hupdate
  simpa [LS.insts, xs, add, Array.toList_modify] using hperm

theorem LS.SymbolWF.appendNoDef {le : LEnv} {scopeCount : Nat} {ls : LS}
    (h : LS.SymbolWF le scopeCount ls) {b : BlockId} (hb : b < ls.blocks.size) (i : Inst)
    (hdefs : ∀ blk, BlockB.defs { blk with insts := blk.insts.push i } = BlockB.defs blk)
    (hi : Inst.SymbolsWithin le scopeCount ls.vals.size ls.blocks.size i) :
    LS.SymbolWF le scopeCount (ls.appendInst b i) := by
  have hperm := LS.insts.modifyPush hb i
  refine ⟨LS.DenseDefinitions.modifyNoNewDefs h.definitions hb _ hdefs, ?_⟩
  intro j hj
  have hj' : j ∈ ls.insts ++ [i] := hperm.mem_iff.mp hj
  rcases List.mem_append.mp hj' with hj' | hj'
  · exact (h.instructions j hj').mono (by simp [LS.appendInst]) (by simp [LS.appendInst])
  · simp at hj'
    subst j
    exact hi.mono (by simp [LS.appendInst]) (by simp [LS.appendInst])

theorem LS.DenseDefinitions.emitDef {op : Op} {le : LEnv} {ls : LS} {b : BlockId}
    (h : ls.DenseDefinitions) (hc : ls.cur = some b) (hb : b < ls.blocks.size) :
    ({ ls with
      vals := ls.vals.push (some (((op.resultTy (tyEnv le ls)).toOption).getD (.data .unit)))
      blocks := ls.blocks.modify b fun blk =>
        { blk with insts := blk.insts.push (.def ls.vals.size op) } }).DenseDefinitions := by
  let add := fun (blk : BlockB) =>
    { blk with insts := blk.insts.push (.def ls.vals.size op) }
  have hblocks :
      ((ls.blocks.modify b add).toList.flatMap BlockB.defs).Perm (ls.defs ++ [ls.vals.size]) := by
    have hi : b < ls.blocks.toList.length := by simpa using hb
    have hupdate : ∀ blk, BlockB.defs (add blk) = BlockB.defs blk ++ [ls.vals.size] := by
      intro blk
      simp [add, BlockB.defs, List.filterMap_append]
    simpa [LS.defs, Array.toList_modify] using
      flatMap_modify_push BlockB.defs ls.blocks.toList b add ls.vals.size hi hupdate
  have hvals : (ls.vals.push (some (((op.resultTy (tyEnv le ls)).toOption).getD (.data .unit)))).size =
      ls.vals.size + 1 := by simp
  rw [LS.DenseDefinitions]
  change List.Perm ((ls.blocks.modify b add).toList.flatMap BlockB.defs)
    (List.range (ls.vals.push (some (((op.resultTy (tyEnv le ls)).toOption).getD (.data .unit)))).size)
  rw [hvals]
  exact hblocks.trans ((h.append_right [ls.vals.size]).trans (by rw [← List.range_succ]))

theorem LS.SymbolWF.emitDef {le : LEnv} {scopeCount : Nat} {ls : LS} {b : BlockId}
    {op : Op} (h : LS.SymbolWF le scopeCount ls) (hc : ls.cur = some b)
    (hb : b < ls.blocks.size)
    (hop : Inst.SymbolsWithin le scopeCount ls.vals.size ls.blocks.size
      (.def ls.vals.size op)) :
    LS.SymbolWF le scopeCount
      { ls with
        vals := ls.vals.push (some (((op.resultTy (tyEnv le ls)).toOption).getD (.data .unit)))
        blocks := ls.blocks.modify b fun blk =>
          { blk with insts := blk.insts.push (.def ls.vals.size op) } } := by
  let i : Inst := .def ls.vals.size op
  let ls' : LS := { ls with
    vals := ls.vals.push (some (((op.resultTy (tyEnv le ls)).toOption).getD (.data .unit)))
    blocks := ls.blocks.modify b fun blk => { blk with insts := blk.insts.push i } }
  have hperm : List.Perm ls'.insts (ls.insts ++ [i]) := by
    simpa [LS.insts, LS.appendInst, ls', i] using LS.insts.modifyPush (ls := ls) hb i
  have hvals : ls.vals.size ≤ ls'.vals.size := by simp [ls']
  have hblocks : ls.blocks.size ≤ ls'.blocks.size := by simp [ls']
  change LS.SymbolWF le scopeCount ls'
  have hdefs := LS.DenseDefinitions.emitDef (le := le) (op := op) h.definitions hc hb
  refine ⟨?_, ?_⟩
  · simpa [LS.DenseDefinitions, LS.defs, ls'] using hdefs
  · intro j hj
    have hj' : j ∈ ls.insts ++ [i] := hperm.mem_iff.mp hj
    rcases List.mem_append.mp hj' with hj' | hj'
    · exact (h.instructions j hj').mono hvals hblocks
    · simp at hj'
      subst j
      exact hop.mono hvals hblocks

theorem LS.SymbolRun.emitDef {le : LEnv} {scopeCount : Nat} {op : Op}
    {ls : LS} (husesBound : ls.cur.isSome → ∀ x ∈ op.uses, x < ls.vals.size)
    (horg : ∀ o, op.origin = some o → o < le.mod.origins.size)
    (hrefs : Op.SymbolRefsValid le op) :
    LS.SymbolRun le scopeCount ls (fun v => [v]) (emitDef op) := by
  intro hls hcur v ls' hrun
  cases hcurr : ls.cur with
  | none =>
    rw [emitDef_none op le hcurr] at hrun
    rcases Prod.mk.inj hrun with ⟨rfl, rfl⟩
    refine ⟨hls, hcur, fun _ => hcurr, ?_⟩
    simp [hcurr]
  | some b =>
    have hb := hcur b hcurr
    rw [emitDef_run op le hcurr] at hrun
    rcases Prod.mk.inj hrun with ⟨rfl, rfl⟩
    have huses : ∀ x ∈ op.uses, x < ls.vals.size := by
      intro x hx
      exact husesBound (by simp [hcurr]) x hx
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply hls.emitDef hcurr hb
      apply Inst.SymbolsWithin.def huses horg hrefs
    · intro b' hb'
      simpa using hcur b' hb'
    · simp [hcurr]
    · intro hlive x hx
      have hx' : x = ls.vals.size := List.mem_singleton.mp hx
      subst x
      simp [Array.size_push]

theorem LS.SymbolRunAt.emitDef {le : LEnv} {scopeCount : Nat} {op : Op}
    {ls : LS} (husesBound : ls.cur.isSome → ∀ x ∈ op.uses, x < ls.vals.size)
    (horg : ∀ o, op.origin = some o → o < le.mod.origins.size)
    (hrefs : Op.SymbolRefsValid le op) :
    LS.SymbolRunAt le scopeCount ls (LS.valueRefs fun v => [v]) (emitDef op) := by
  exact (LS.SymbolRun.emitDef husesBound horg hrefs).toSymbolRunAt (advB_emitDef op)

theorem LS.SymbolRun.emitEffect {le : LEnv} {scopeCount : Nat} (e : Effect)
    {ls : LS} (husesBound : ls.cur.isSome → ∀ x ∈ e.uses, x < ls.vals.size)
    (horg : ∀ o, e.origin = some o → o < le.mod.origins.size)
    (hrefs : Effect.SymbolRefsValid le scopeCount e) :
    LS.SymbolRun le scopeCount ls (fun _ : Unit => []) (emitEffect e) := by
  intro hls hc a ls' hrun
  cases hcurr : ls.cur with
  | none =>
    rw [emitEffect_none e le hcurr] at hrun
    rcases Prod.mk.inj hrun with ⟨rfl, rfl⟩
    exact ⟨hls, hc, fun _ => hcurr, by simp⟩
  | some b =>
    rw [emitEffect_run e le hcurr] at hrun
    rcases Prod.mk.inj hrun with ⟨rfl, rfl⟩
    have hb := hc b hcurr
    have huses : ∀ x ∈ e.uses, x < ls.vals.size := by
      intro x hx
      exact husesBound (by simp [hcurr]) x hx
    have hnext := hls.appendNoDef hb (.eff e) (by
      intro blk
      simp [BlockB.defs, List.filterMap_append]) (Inst.SymbolsWithin.eff huses horg hrefs)
    refine ⟨by simpa [LS.appendInst] using hnext, ?_, ?_, by simp⟩
    · intro b' hb'
      simpa using hc b' hb'
    · simp [hcurr]

theorem LS.SymbolRun.emitTerm {le : LEnv} {scopeCount : Nat} (t : Term)
    {ls : LS} (husesBound : ls.cur.isSome → ∀ x ∈ t.uses, x < ls.vals.size)
    (horg : ∀ o, t.origin = some o → o < le.mod.origins.size)
    (htargets : ∀ b ∈ t.successors, b < ls.blocks.size) :
    LS.SymbolRun le scopeCount ls (fun _ : Unit => []) (emitTerm t) := by
  intro hls hc a ls' hrun
  cases hcurr : ls.cur with
  | none =>
    rw [emitTerm_none t le hcurr] at hrun
    rcases Prod.mk.inj hrun with ⟨rfl, rfl⟩
    exact ⟨hls, hc, fun _ => hcurr, by simp⟩
  | some b =>
    rw [emitTerm_run t le hcurr] at hrun
    rcases Prod.mk.inj hrun with ⟨rfl, rfl⟩
    have huses : ∀ x ∈ t.uses, x < ls.vals.size := by
      intro x hx
      exact husesBound (by simp [hcurr]) x hx
    have hwithin : Inst.SymbolsWithin le scopeCount ls.vals.size ls.blocks.size (.term t) := by
      apply Inst.SymbolsWithin.term huses horg
      intro target htarget
      exact htargets target htarget
    have happend := hls.appendNoDef (hc b hcurr) (.term t) (by
      intro blk
      simp [BlockB.defs, List.filterMap_append]) hwithin
    have hnextBase : LS.SymbolWF le scopeCount
        { ls with blocks := ls.blocks.modify b fun blk =>
          { blk with insts := blk.insts.push (.term t) } } := by
      simpa [LS.appendInst] using happend
    have hnext := hnextBase.changeCur none
    refine ⟨hnext, ?_, fun _ => rfl, ?_⟩
    · intro target htarget
      simp [LS.CurrentBlocks] at htarget
    · intro live x hx
      simp at hx

theorem LS.DenseDefinitions.emitEffect {e : Effect} {le : LEnv} {ls : LS} {b : BlockId}
    (h : ls.DenseDefinitions) (hb : b < ls.blocks.size) :
    ({ ls with blocks := ls.blocks.modify b fun blk =>
      { blk with insts := blk.insts.push (.eff e) } }).DenseDefinitions := by
  apply LS.DenseDefinitions.modifyNoNewDefs h hb
  intro blk
  simp [BlockB.defs, List.filterMap_append]

theorem LS.SymbolWF.emitEffect {e : Effect} {le : LEnv} {scopeCount : Nat} {ls : LS}
    {b : BlockId} (h : LS.SymbolWF le scopeCount ls) (hb : b < ls.blocks.size)
    (he : Inst.SymbolsWithin le scopeCount ls.vals.size ls.blocks.size (.eff e)) :
    LS.SymbolWF le scopeCount
      { ls with blocks := ls.blocks.modify b fun blk =>
        { blk with insts := blk.insts.push (.eff e) } } := by
  have h' := h.appendNoDef hb (.eff e) (by
    intro blk
    simp [BlockB.defs, List.filterMap_append]) he
  simpa [LS.appendInst] using h'

theorem LS.DenseDefinitions.emitTerm {t : Term} {le : LEnv} {ls : LS} {b : BlockId}
    (h : ls.DenseDefinitions) (hb : b < ls.blocks.size) :
    ({ ls with blocks := ls.blocks.modify b fun blk =>
      { blk with insts := blk.insts.push (.term t) }, cur := none }).DenseDefinitions := by
  have h' := LS.DenseDefinitions.modifyNoNewDefs h hb (fun blk =>
    { blk with insts := blk.insts.push (.term t) }) (by
      intro blk
      simp [BlockB.defs, List.filterMap_append])
  simpa [LS.DenseDefinitions, LS.defs] using h'

theorem LS.SymbolWF.emitTerm {t : Term} {le : LEnv} {scopeCount : Nat} {ls : LS}
    {b : BlockId} (h : LS.SymbolWF le scopeCount ls) (hb : b < ls.blocks.size)
    (ht : Inst.SymbolsWithin le scopeCount ls.vals.size ls.blocks.size (.term t)) :
    LS.SymbolWF le scopeCount
      { ls with blocks := ls.blocks.modify b fun blk =>
        { blk with insts := blk.insts.push (.term t) }, cur := none } := by
  have h' := h.appendNoDef hb (.term t) (by
    intro blk
    simp [BlockB.defs, List.filterMap_append]) ht
  have h'' := h'.changeCur none
  simpa [LS.appendInst] using h''

theorem LS.SymbolWF.fork {cv : ValueId} {le : LEnv} {scopeCount : Nat} {ls : LS}
    {b : BlockId} (h : LS.SymbolWF le scopeCount ls) (hc : ls.cur = some b)
    (hb : b < ls.blocks.size) (hcv : cv < ls.vals.size) :
    LS.SymbolWF le scopeCount (fork cv le ls).2 := by
  let b1 := ls.blocks.size
  let b2 := ls.blocks.size + 1
  let ls1 : LS := { ls with blocks := ls.blocks.push ⟨[], #[]⟩ }
  let ls2 : LS := { ls1 with blocks := ls1.blocks.push ⟨[], #[]⟩ }
  have h1 : LS.SymbolWF le scopeCount ls1 := by
    simpa [ls1, paramIds, pushParamTypes] using
      (LS.SymbolWF.newBlock (tys := []) (le := le) h)
  have h2 : LS.SymbolWF le scopeCount ls2 := by
    simpa [ls2, paramIds, pushParamTypes] using
      (LS.SymbolWF.newBlock (tys := []) (le := le) h1)
  have hb2 : b < ls2.blocks.size := by
    simp only [ls2, ls1, Array.size_push]
    nat_omega
  have hterm : Inst.SymbolsWithin le scopeCount ls2.vals.size ls2.blocks.size
      (.term (.condbr cv b1 [] b2 [])) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Inst.uses, Term.uses]
      exact hcv
    · simp [Inst.origin, Term.origin]
    · simp [instSlotRefs]
    · simp [instGlobalRefs]
    · simp [instFunctionRefs]
    · simp [instScopeRefs]
    · intro target ht
      simp [instTargetRefs, Term.successors] at ht
      rcases ht with rfl | rfl
      · simp only [b1]
        simp only [ls2, ls1, Array.size_push]
        nat_omega
      · simp only [b2]
        simp only [ls2, ls1, Array.size_push]
        nat_omega
  have h3 := LS.SymbolWF.emitTerm h2 hb2 hterm
  rw [fork_run cv le hc]
  simpa [b1, b2, ls1, ls2, paramIds, pushParamTypes] using h3

theorem LS.DenseDefinitions.patchTerm {t : Term} {le : LEnv} {ls : LS} {b : BlockId}
    (h : ls.DenseDefinitions) (hb : b < ls.blocks.size) :
    ({ ls with blocks := ls.blocks.modify b fun blk =>
      { blk with insts := blk.insts.push (.term t) } }).DenseDefinitions := by
  apply LS.DenseDefinitions.modifyNoNewDefs h hb
  intro blk
  simp [BlockB.defs, List.filterMap_append]

theorem LS.SymbolWF.patchTerm {t : Term} {le : LEnv} {scopeCount : Nat} {ls : LS}
    {b : BlockId} (h : LS.SymbolWF le scopeCount ls) (hb : b < ls.blocks.size)
    (ht : Inst.SymbolsWithin le scopeCount ls.vals.size ls.blocks.size (.term t)) :
    LS.SymbolWF le scopeCount
      { ls with blocks := ls.blocks.modify b fun blk =>
        { blk with insts := blk.insts.push (.term t) } } := by
  have h' := h.appendNoDef hb (.term t) (by
    intro blk
    simp [BlockB.defs, List.filterMap_append]) ht
  simpa [LS.appendInst] using h'

theorem lowerExpr_lit_symbols {le : LEnv} {scopeCount : Nat} {ls : LS} {b : BlockId}
    (h : LS.SymbolWF le scopeCount ls) (hc : ls.cur = some b) (hb : b < ls.blocks.size)
    (t : Goose.Core.IntTy) (n : Int) :
    LS.SymbolWF le scopeCount (lowerExpr (.lit t n) le ls).2 := by
  change LS.SymbolWF le scopeCount (emitDef (.constInt t n) le ls).2
  rw [emitDef_run _ _ hc]
  apply LS.SymbolWF.emitDef h hc hb
  apply Inst.SymbolsWithin.def
  · simp [Op.uses]
  · simp [Op.origin]
  · simp [Op.SymbolRefsValid]

theorem lowerExpr_bool_symbols {le : LEnv} {scopeCount : Nat} {ls : LS} {b : BlockId}
    (h : LS.SymbolWF le scopeCount ls) (hc : ls.cur = some b) (hb : b < ls.blocks.size)
    (value : Bool) :
    LS.SymbolWF le scopeCount (lowerExpr (.bool value) le ls).2 := by
  change LS.SymbolWF le scopeCount (emitDef (.constBool value) le ls).2
  rw [emitDef_run _ _ hc]
  apply LS.SymbolWF.emitDef h hc hb
  apply Inst.SymbolsWithin.def
  · simp [Op.uses]
  · simp [Op.origin]
  · simp [Op.SymbolRefsValid]

theorem lowerPlace_var_symbols {le : LEnv} {scopeCount : Nat} {ls : LS} {b : BlockId}
    (h : LS.SymbolWF le scopeCount ls) (hc : ls.cur = some b) (hb : b < ls.blocks.size)
    (x : Goose.Core.VarId) (hx : x < le.slots.size) :
    LS.SymbolWF le scopeCount (lowerPlace (.var x) le ls).2 := by
  change LS.SymbolWF le scopeCount (emitDef (.slotAddr x) le ls).2
  rw [emitDef_run _ _ hc]
  apply LS.SymbolWF.emitDef h hc hb
  apply Inst.SymbolsWithin.def
  · simp [Op.uses]
  · simp [Op.origin]
  · simpa [Op.SymbolRefsValid] using hx

theorem lowerExpr_lit_symbolRun {le : LEnv} {scopeCount : Nat} (t : Goose.Core.IntTy)
    {ls : LS} (n : Int) :
    LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerExpr (.lit t n)) := by
  change LS.SymbolRun le scopeCount ls (fun v => [v]) (emitDef (.constInt t n))
  apply LS.SymbolRun.emitDef
  · intro hlive v hv
    simp [Op.uses] at hv
  · intro o ho
    simp [Op.origin] at ho
  · simp [Op.SymbolRefsValid]

theorem lowerExpr_bool_symbolRun {le : LEnv} {scopeCount : Nat} {ls : LS} (value : Bool) :
    LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerExpr (.bool value)) := by
  change LS.SymbolRun le scopeCount ls (fun v => [v]) (emitDef (.constBool value))
  apply LS.SymbolRun.emitDef
  · intro hlive v hv
    simp [Op.uses] at hv
  · intro o ho
    simp [Op.origin] at ho
  · simp [Op.SymbolRefsValid]

theorem lowerPlace_var_symbolRun {le : LEnv} {scopeCount : Nat} (x : Goose.Core.VarId)
    {ls : LS} (hx : x < le.slots.size) :
    LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerPlace (.var x)) := by
  change LS.SymbolRun le scopeCount ls (fun v => [v]) (emitDef (.slotAddr x))
  apply LS.SymbolRun.emitDef
  · intro hlive v hv
    simp [Op.uses] at hv
  · intro o ho
    simp [Op.origin] at ho
  · simpa [Op.SymbolRefsValid] using hx

theorem lowerPlace_global_symbolRun {le : LEnv} {scopeCount : Nat}
    (g : Goose.Core.GlobalId) {ls : LS} (hg : g < le.globals.size) :
    LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerPlace (.global g)) := by
  change LS.SymbolRun le scopeCount ls (fun v => [v]) (emitDef (.globalAddr g))
  apply LS.SymbolRun.emitDef
  · intro hlive v hv
    simp [Op.uses] at hv
  · intro o ho
    simp [Op.origin] at ho
  · simpa [Op.SymbolRefsValid] using hg

theorem lowerPlace_field_symbolRun_of {le : LEnv} {scopeCount : Nat}
    {owner : Goose.Core.Place}
    (howner : ∀ ls, LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerPlace owner)) :
    ∀ i ls, LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerPlace (.field owner i)) := by
  intro i ls
  change LS.SymbolRun le scopeCount ls (fun v => [v])
    (do let r ← lowerPlace owner; emitDef (.fieldAddr r i))
  apply LS.SymbolRun.bind (howner ls)
  intro r mid hmid hcMid hr
  apply LS.SymbolRun.emitDef
  · intro live v hv
    simp [Op.uses] at hv
    subst v
    exact hr live r (by simp)
  · intro o ho
    simp [Op.origin] at ho
  · simp [Op.SymbolRefsValid]

theorem lowerExpr_read_var_symbolRun {le : LEnv} {scopeCount : Nat} (x : Goose.Core.VarId)
    {ls : LS} (hx : x < le.slots.size) :
    LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerExpr (.read (.var x))) := by
  change LS.SymbolRun le scopeCount ls (fun v => [v])
    (do let r ← lowerPlace (.var x); emitDef (.load r))
  apply LS.SymbolRun.bind (lowerPlace_var_symbolRun x hx)
  intro r ls hls hc hr
  apply LS.SymbolRun.emitDef
  · intro live u hu
    simp [Op.uses] at hu
    subst u
    exact hr live r (by simp)
  · intro o ho
    simp [Op.origin] at ho
  · simp [Op.SymbolRefsValid]

theorem lowerExpr_read_symbolRun_of {le : LEnv} {scopeCount : Nat}
    {p : Goose.Core.Place} {ls : LS}
    (hplace : LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerPlace p)) :
    LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerExpr (.read p)) := by
  change LS.SymbolRun le scopeCount ls (fun v => [v])
    (do let r ← lowerPlace p; emitDef (.load r))
  apply LS.SymbolRun.bind hplace
  intro r ls1 hls1 hc1 hr
  apply LS.SymbolRun.emitDef
  · intro live u hu
    simp [Op.uses] at hu
    subst u
    exact hr live r (by simp)
  · intro o ho
    simp [Op.origin] at ho
  · simp [Op.SymbolRefsValid]

theorem lowerExpr_un_symbolRun_of {le : LEnv} {scopeCount : Nat} {e : Goose.Core.Expr}
    (hexpr : ∀ ls, LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerExpr e)) :
    ∀ o, o < le.mod.origins.size → ∀ op ls,
      LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerExpr (.un op e o)) := by
  intro o horg op ls
  have hrunAt : LS.SymbolRunAt le scopeCount ls
      (LS.valueRefs fun v => [v]) (lowerExpr (.un op e o)) := by
    change LS.SymbolRunAt le scopeCount ls (LS.valueRefs fun v => [v])
      (do let a ← lowerExpr e
          emitDef (.un op (← intTyOf a) a (some o)))
    apply LS.SymbolRunAt.bind ((hexpr ls).toSymbolRunAt (advB_lowerExpr e))
    intro a mid hmid hcMid hrefs hadv hdead
    change LS.SymbolRunAt le scopeCount mid (LS.valueRefs fun v => [v])
      (intTyOf a >>= fun t => emitDef (.un op t a (some o)))
    have hstable : ∃ t, intTyOf a le mid = (t, mid) := by
      refine ⟨(intTyOf a le mid).1, Prod.ext rfl ?_⟩
      exact intTyOf_state a le mid
    have hty : LS.SymbolRunAt le scopeCount mid (fun _ _ => []) (intTyOf a) :=
      LS.SymbolRunAt.stable hstable (by simp)
    apply LS.SymbolRunAt.bind hty
    intro t mid2 hmid2 hcMid2 _ hadv2 hdead2
    apply LS.SymbolRunAt.emitDef
    · intro live u hu
      simp [Op.uses] at hu
      subst u
      have hmidLive : mid.cur.isSome := by
        cases hcur : mid.cur with
        | none =>
          have hclosed := hdead2 hcur
          simp [hclosed] at live
        | some _ => simp
      have hmem : SymbolRef.value a ∈ LS.valueRefs (fun v : ValueId => [v]) a mid := by
        simp [LS.valueRefs, hmidLive]
      have hbound := hrefs (.value a) hmem
      change a < mid.vals.size at hbound
      exact Nat.lt_of_lt_of_le hbound hadv2.vals
    · intro o' ho
      simp [Op.origin] at ho
      subst o'
      exact horg
    · simp [Op.SymbolRefsValid]
  exact hrunAt.toSymbolRun

theorem lowerExpr_bin_symbolRun_of {le : LEnv} {scopeCount : Nat}
    {a b : Goose.Core.Expr}
    (hleft : ∀ ls, LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerExpr a))
    (hright : ∀ ls, LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerExpr b)) :
    ∀ o, o < le.mod.origins.size → ∀ op ls,
      LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerExpr (.bin op a b o)) := by
  intro o horg op ls
  have hrunAt : LS.SymbolRunAt le scopeCount ls
      (LS.valueRefs fun v => [v]) (lowerExpr (.bin op a b o)) := by
    change LS.SymbolRunAt le scopeCount ls (LS.valueRefs fun v => [v])
      (do let x ← lowerExpr a
          let y ← lowerExpr b
          emitDef (.bin op (← intTyOf x) x y (some o)))
    apply LS.SymbolRunAt.bind ((hleft ls).toSymbolRunAt (advB_lowerExpr a))
    intro x mid hmid hcMid hrefsX hadvX hdeadX
    apply LS.SymbolRunAt.bind ((hright mid).toSymbolRunAt (advB_lowerExpr b))
    intro y mid2 hmid2 hcMid2 hrefsY hadvY hdeadY
    change LS.SymbolRunAt le scopeCount mid2
      (LS.valueRefs fun v => [v])
      (intTyOf x >>= fun t => emitDef (.bin op t x y (some o)))
    have hstable : ∃ t, intTyOf x le mid2 = (t, mid2) := by
      refine ⟨(intTyOf x le mid2).1, Prod.ext rfl ?_⟩
      exact intTyOf_state x le mid2
    have hty : LS.SymbolRunAt le scopeCount mid2 (fun _ _ => []) (intTyOf x) :=
      LS.SymbolRunAt.stable hstable (by simp)
    apply LS.SymbolRunAt.bind hty
    intro t mid3 hmid3 hcMid3 _ hadv3 hdead3
    apply LS.SymbolRunAt.emitDef
    · intro live u hu
      simp [Op.uses] at hu
      rcases hu with hux | huy
      · have hmidLive : mid.cur.isSome := by
          cases hcur : mid.cur with
          | none =>
            have hclosed2 := hdeadY hcur
            have hclosed3 := hdead3 hclosed2
            simp [hclosed3] at live
          | some _ => simp
        subst u
        have hmem : SymbolRef.value x ∈ LS.valueRefs (fun v : ValueId => [v]) x mid := by
          simp [LS.valueRefs, hmidLive]
        have hbound := hrefsX (.value x) hmem
        change x < mid.vals.size at hbound
        exact Nat.lt_of_lt_of_le hbound (Nat.le_trans hadvY.vals hadv3.vals)
      · have hmid2Live : mid2.cur.isSome := by
          cases hcur : mid2.cur with
          | none =>
            have hclosed := hdead3 hcur
            simp [hclosed] at live
          | some _ => simp
        subst u
        have hmem : SymbolRef.value y ∈ LS.valueRefs (fun v : ValueId => [v]) y mid2 := by
          simp [LS.valueRefs, hmid2Live]
        have hbound := hrefsY (.value y) hmem
        change y < mid2.vals.size at hbound
        exact Nat.lt_of_lt_of_le hbound hadv3.vals
    · intro o' ho
      simp [Op.origin] at ho
      subst o'
      exact horg
    · simp [Op.SymbolRefsValid]
  exact hrunAt.toSymbolRun

theorem lowerExpr_cmp_symbolRun_of {le : LEnv} {scopeCount : Nat}
    {a b : Goose.Core.Expr}
    (hleft : ∀ ls, LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerExpr a))
    (hright : ∀ ls, LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerExpr b)) :
    ∀ op ls,
      LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerExpr (.cmp op a b)) := by
  intro op ls
  have hrunAt : LS.SymbolRunAt le scopeCount ls
      (LS.valueRefs fun v => [v]) (lowerExpr (.cmp op a b)) := by
    change LS.SymbolRunAt le scopeCount ls (LS.valueRefs fun v => [v])
      (do let x ← lowerExpr a
          let y ← lowerExpr b
          match (← valTy x) with
          | .data (.int t) => emitDef (.cmp op t x y)
          | _ => emitDef (.boolCmp op x y))
    apply LS.SymbolRunAt.bind ((hleft ls).toSymbolRunAt (advB_lowerExpr a))
    intro x mid hmid hcMid hrefsX hadvX hdeadX
    apply LS.SymbolRunAt.bind ((hright mid).toSymbolRunAt (advB_lowerExpr b))
    intro y mid2 hmid2 hcMid2 hrefsY hadvY hdeadY
    change LS.SymbolRunAt le scopeCount mid2 (LS.valueRefs fun v => [v])
      (valTy x >>= fun ty =>
        match ty with
        | .data (.int t) => emitDef (.cmp op t x y)
        | _ => emitDef (.boolCmp op x y))
    have hstable : ∃ ty, valTy x le mid2 = (ty, mid2) := by
      refine ⟨(valTy x le mid2).1, Prod.ext rfl ?_⟩
      exact valTy_run x le mid2
    have hty : LS.SymbolRunAt le scopeCount mid2 (fun _ _ => []) (valTy x) :=
      LS.SymbolRunAt.stable hstable (by simp)
    apply LS.SymbolRunAt.bind hty
    intro ty mid3 hmid3 hcMid3 _ hadv3 hdead3
    have hoperBound : ∀ (live : mid3.cur.isSome) (v : ValueId),
        v ∈ [x, y] → v < mid3.vals.size := by
      intro live v hv
      rcases List.mem_cons.mp hv with hvx | hvy
      · have hvxEq : v = x := by simpa using hvx
        subst v
        have hmidLive : mid.cur.isSome := by
          cases hcur : mid.cur with
          | none =>
            have hclosed2 := hdeadY hcur
            have hclosed3 := hdead3 hclosed2
            simp [hclosed3] at live
          | some _ => simp
        have hmem : SymbolRef.value x ∈ LS.valueRefs (fun v : ValueId => [v]) x mid := by
          simp [LS.valueRefs, hmidLive]
        have hbound := hrefsX (.value x) hmem
        change x < mid.vals.size at hbound
        exact Nat.lt_of_lt_of_le hbound (Nat.le_trans hadvY.vals hadv3.vals)
      · have hvyEq : v = y := by simpa using hvy
        subst v
        have hmid2Live : mid2.cur.isSome := by
          cases hcur : mid2.cur with
          | none =>
            have hclosed := hdead3 hcur
            simp [hclosed] at live
          | some _ => simp
        have hmem : SymbolRef.value y ∈ LS.valueRefs (fun v : ValueId => [v]) y mid2 := by
          simp [LS.valueRefs, hmid2Live]
        have hbound := hrefsY (.value y) hmem
        change y < mid2.vals.size at hbound
        exact Nat.lt_of_lt_of_le hbound hadv3.vals
    have hrunDef (q : Op) (huses : ∀ v ∈ q.uses, v ∈ [x, y])
        (horg : ∀ o, q.origin = some o → o < le.mod.origins.size)
        (hrefs : Op.SymbolRefsValid le q) :
        LS.SymbolRunAt le scopeCount mid3 (LS.valueRefs fun v => [v]) (emitDef q) := by
      apply LS.SymbolRunAt.emitDef
      · intro live v hv
        exact hoperBound live v (huses v hv)
      · exact horg
      · exact hrefs
    cases ty with
    | data t =>
      cases t with
      | int t =>
        change LS.SymbolRunAt le scopeCount mid3 (LS.valueRefs fun v => [v])
          (emitDef (.cmp op t x y))
        exact hrunDef _ (by simp [Op.uses])
          (by intro o ho; simp [Op.origin] at ho) (by simp [Op.SymbolRefsValid])
      | _ =>
        change LS.SymbolRunAt le scopeCount mid3 (LS.valueRefs fun v => [v])
          (emitDef (.boolCmp op x y))
        exact hrunDef _ (by simp [Op.uses])
          (by intro o ho; simp [Op.origin] at ho) (by simp [Op.SymbolRefsValid])
    | view _ _ =>
      change LS.SymbolRunAt le scopeCount mid3 (LS.valueRefs fun v => [v])
        (emitDef (.boolCmp op x y))
      exact hrunDef _ (by simp [Op.uses])
        (by intro o ho; simp [Op.origin] at ho) (by simp [Op.SymbolRefsValid])
  exact hrunAt.toSymbolRun

theorem lowerExprs_symbolRun_of {le : LEnv} {scopeCount : Nat} :
    ∀ es : List Goose.Core.Expr,
      (∀ e ∈ es, ∀ ls, LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerExpr e)) →
      ∀ ls,
      LS.SymbolRun le scopeCount ls (fun vs => vs) (lowerExprs es) := by
  intro es
  induction es with
  | nil =>
    intro _ ls hls hcur vs ls' hrun
    simp only [lowerExprs, pure_run] at hrun
    rcases Prod.mk.inj hrun with ⟨rfl, rfl⟩
    refine ⟨hls, hcur, ?_, ?_⟩
    · exact fun h => h
    · intro hlive v hv
      simp at hv
  | cons e rest ih =>
    intro hexpr ls hls hcur vs ls' hrun
    simp only [lowerExprs, bind_eq] at hrun
    obtain ⟨v, ls1, h1, vs', ls2, h2, h3⟩ := hrun
    rw [pure_run] at h3
    rcases Prod.mk.inj h3 with ⟨rfl, rfl⟩
    obtain ⟨hls1, hc1, hdead1, hids1⟩ := hexpr e (by simp) ls hls hcur v ls1 h1
    obtain ⟨hls2, hc2, hdead2, hids2⟩ :=
      ih (by
        intro e' he'
        exact hexpr e' (by simp [he'])) ls1 hls1 hc1 vs' ls2 h2
    have hadv := advB_lowerExprs rest le ls1 vs' ls2 h2
    refine ⟨hls2, hc2, ?_, ?_⟩
    · intro hdead
      exact hdead2 (hdead1 hdead)
    · intro hlive x hx
      rcases List.mem_cons.mp hx with hxv | hxrest
      · have hls1live : ls1.cur.isSome := by
          cases hcur1 : ls1.cur with
          | none =>
            have := hdead2 hcur1
            simp [this] at hlive
          | some _ => simp
        have hv := hids1 hls1live x (by simpa using hxv)
        exact Nat.lt_of_lt_of_le hv hadv.vals
      · exact hids2 hlive x hxrest

theorem LS.denseDefinitions_initState : initState.DenseDefinitions := by
  simp [LS.DenseDefinitions, LS.defs, initState]

theorem LS.symbolWF_initState (le : LEnv) (scopeCount : Nat) :
    LS.SymbolWF le scopeCount initState := by
  refine ⟨LS.denseDefinitions_initState, ?_⟩
  intro i hi
  simp [LS.insts, initState] at hi

theorem lowerImplAt_start_symbols (m : Goose.Core.Module) (impl : Goose.Core.Impl)
    (implId scopeCount : Nat) :
    let le := lowerEnv m impl.vars
    let start := Goose.Lower.newBlock (impl.params.toList.map fun p => .data (tyOfVar impl p.var))
      le initState
    LS.SymbolWF le scopeCount
      { start.2 with cur := some start.1.1 } := by
  dsimp
  exact (LS.symbolWF_initState (lowerEnv m impl.vars) scopeCount).newBlockCur

theorem finishBlocks_defs (blocks : Array BlockB) :
    (finishBlocks blocks).toList.flatMap GIR.Block.defs =
      blocks.toList.flatMap BlockB.defs := by
  simp only [finishBlocks, Array.toList_map, List.flatMap_map]
  rfl

/-! Successful Core place typing certifies the source table indices that lowering emits. -/
theorem Core.tyPlace_var_success_bound {env : Core.TEnv} {x : Core.VarId}
    {fuel : Nat} {info : Core.PlaceInfo} {fuel' : Nat}
    (h : (Core.tyPlace env (.var x)).run fuel = .ok (info, fuel')) :
    x < env.vars.size := by
  cases hvar : env.vars[x]? with
  | none =>
    cases hv : env.visible.contains x
    · have hnot : x ∉ env.visible := by
        intro hm
        have hc : env.visible.contains x = true := List.contains_iff_mem.mpr hm
        rw [hv] at hc
        contradiction
      simp [Core.tyPlace, Core.varOf, hnot, Core.rej] at h
      change (Except.error _ : Core.V (Core.PlaceInfo × Nat)) = .ok _ at h
      cases h
    · have hm : x ∈ env.visible := List.contains_iff_mem.mp hv
      simp [Core.tyPlace, Core.varOf, hvar, hm, Core.rej] at h
      change (Except.error _ : Core.V (Core.PlaceInfo × Nat)) = .ok _ at h
      cases h
  | some lv => exact (Array.getElem?_eq_some_iff.mp hvar).1

theorem Core.tyPlace_global_success_bound {env : Core.TEnv} {g : Core.GlobalId}
    {fuel : Nat} {info : Core.PlaceInfo} {fuel' : Nat}
    (h : (Core.tyPlace env (.global g)).run fuel = .ok (info, fuel')) :
    g < env.globalLimit := by
  by_cases hlimit : g < env.globalLimit
  · exact hlimit
  · simp [Core.tyPlace, hlimit, Core.rej] at h
    change (Except.error _ : Core.V (Core.PlaceInfo × Nat)) = .ok _ at h
    cases h

theorem Core.tyPlace_elem_success_origin_bound {env : Core.TEnv} {v : Core.View}
    {i : Core.Expr} {org : Core.OriginId} {fuel : Nat}
    {info : Core.PlaceInfo} {fuel' : Nat}
    (h : (Core.tyPlace env (.elem v i org)).run fuel = .ok (info, fuel')) :
    org < env.mod.origins.size := by
  by_cases horg : org < env.mod.origins.size
  · exact horg
  · simp [Core.tyPlace, Core.checkOrg, Core.rej, horg] at h
    change (Except.error _ : Core.V (Core.PlaceInfo × Nat)) = .ok _ at h
    cases h

theorem lowerEnv_slots_size (m : Core.Module) (vars : Array Core.LocalVar) :
    (lowerEnv m vars).slots.size = vars.size := by
  simp [lowerEnv]

theorem lowerEnv_globals_size (m : Core.Module) (vars : Array Core.LocalVar) :
    (lowerEnv m vars).globals.size = m.globals.size := by
  simp [lowerEnv]

theorem lowerEnv_sigs_size (m : Core.Module) (vars : Array Core.LocalVar) :
    (lowerEnv m vars).sigs.size = m.impls.size := by
  simp [lowerEnv]

theorem lowerPlace_var_symbolRun_of_tyPlace {le : LEnv} {scopeCount : Nat}
    {env : Core.TEnv} {x : Core.VarId} {fuel : Nat} {info : Core.PlaceInfo} {fuel' : Nat}
    (h : (Core.tyPlace env (.var x)).run fuel = .ok (info, fuel'))
    (hslots : env.vars.size = le.slots.size) {ls : LS} :
    LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerPlace (.var x)) := by
  apply lowerPlace_var_symbolRun
  rw [← hslots]
  exact Core.tyPlace_var_success_bound h

theorem lowerPlace_var_symbolRun_of_tyPlace_lowerEnv {m : Core.Module}
    {vars : Array Core.LocalVar} {scopeCount : Nat} {env : Core.TEnv}
    {x : Core.VarId} {fuel : Nat} {info : Core.PlaceInfo} {fuel' : Nat}
    (hvars : env.vars = vars)
    (h : (Core.tyPlace env (.var x)).run fuel = .ok (info, fuel')) {ls : LS} :
    LS.SymbolRun (lowerEnv m vars) scopeCount ls (fun v => [v]) (lowerPlace (.var x)) := by
  apply lowerPlace_var_symbolRun_of_tyPlace h
  simp [lowerEnv, hvars]

theorem lowerPlace_global_symbolRun_of_tyPlace {le : LEnv} {scopeCount : Nat}
    {env : Core.TEnv} {g : Core.GlobalId} {fuel : Nat} {info : Core.PlaceInfo} {fuel' : Nat}
    (h : (Core.tyPlace env (.global g)).run fuel = .ok (info, fuel'))
    (hglobals : env.globalLimit ≤ le.globals.size) {ls : LS} :
    LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerPlace (.global g)) := by
  apply lowerPlace_global_symbolRun
  exact Nat.lt_of_lt_of_le (Core.tyPlace_global_success_bound h) hglobals

theorem lowerPlace_global_symbolRun_of_tyPlace_lowerEnv {m : Core.Module}
    {vars : Array Core.LocalVar} {scopeCount : Nat} {env : Core.TEnv}
    {g : Core.GlobalId} {fuel : Nat} {info : Core.PlaceInfo} {fuel' : Nat}
    (hlimit : env.globalLimit ≤ m.globals.size)
    (h : (Core.tyPlace env (.global g)).run fuel = .ok (info, fuel')) {ls : LS} :
    LS.SymbolRun (lowerEnv m vars) scopeCount ls (fun v => [v]) (lowerPlace (.global g)) := by
  apply lowerPlace_global_symbolRun_of_tyPlace h
  simpa [lowerEnv] using hlimit

theorem lowerPlace_deref_symbolRun_of {le : LEnv} {scopeCount : Nat}
    {e : Core.Expr} (hexpr : ∀ ls,
      LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerExpr e)) :
    ∀ ls, LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerPlace (.deref e)) := by
  intro ls
  simpa [lowerPlace] using hexpr ls

theorem lowerPlace_snapshot_symbolRun_of {le : LEnv} {scopeCount : Nat}
    {p : Core.Place} (mode : Goose.GIR.SnapshotMode) (hplace : ∀ ls,
      LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerPlace p)) :
    ∀ ls, LS.SymbolRun le scopeCount ls (fun v => [v])
      (do let r ← lowerPlace p; emitDef (.snapshot mode r)) := by
  intro ls
  have hrunAt : LS.SymbolRunAt le scopeCount ls (LS.valueRefs fun v => [v])
      (do let r ← lowerPlace p; emitDef (.snapshot mode r)) := by
    change LS.SymbolRunAt le scopeCount ls (LS.valueRefs fun v => [v])
      (do let r ← lowerPlace p
          emitDef (.snapshot mode r))
    apply LS.SymbolRunAt.bind ((hplace ls).toSymbolRunAt (advB_lowerPlace p))
    intro r mid hmid hcur hrefs hadv hdead
    apply LS.SymbolRunAt.emitDef
    · intro live v hv
      simp [Op.uses] at hv
      subst v
      have hmem : SymbolRef.value r ∈ LS.valueRefs (fun v : ValueId => [v]) r mid := by
        simp [LS.valueRefs, live]
      have hbound := hrefs (.value r) hmem
      change r < mid.vals.size at hbound
      exact hbound
    · intro o ho
      simp [Op.origin] at ho
    · simp [Op.SymbolRefsValid]
  exact hrunAt.toSymbolRun

theorem lowerView_of_symbolRun_of {le : LEnv} {scopeCount : Nat}
    {p : Core.Place} (hplace : ∀ ls,
      LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerPlace p)) :
    ∀ ls, LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerView (.of p)) := by
  cases p with
  | var x =>
    intro ls
    simpa [lowerView] using lowerPlace_snapshot_symbolRun_of .owner hplace ls
  | global g =>
    intro ls
    simpa [lowerView] using lowerPlace_snapshot_symbolRun_of .owner hplace ls
  | deref e =>
    intro ls
    simpa [lowerView] using lowerPlace_snapshot_symbolRun_of .borrowed hplace ls
  | elem v i o =>
    intro ls
    simpa [lowerView] using lowerPlace_snapshot_symbolRun_of .borrowed hplace ls
  | field owner i =>
    intro ls
    simpa [lowerView] using lowerPlace_snapshot_symbolRun_of .borrowed hplace ls

theorem lowerView_val_symbolRun_of {le : LEnv} {scopeCount : Nat}
    {e : Core.Expr} (hexpr : ∀ ls,
      LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerExpr e)) :
    ∀ ls, LS.SymbolRun le scopeCount ls (fun v => [v]) (lowerView (.val e)) := by
  intro ls
  have hrunAt : LS.SymbolRunAt le scopeCount ls (LS.valueRefs fun v => [v])
      (lowerView (.val e)) := by
    change LS.SymbolRunAt le scopeCount ls (LS.valueRefs fun v => [v])
      (do let s ← lowerExpr e; emitDef (.sliceView s))
    apply LS.SymbolRunAt.bind ((hexpr ls).toSymbolRunAt (advB_lowerExpr e))
    intro s mid hmid hcur hrefs hadv hdead
    apply LS.SymbolRunAt.emitDef
    · intro live v hv
      simp [Op.uses] at hv
      subst v
      have hmem : SymbolRef.value s ∈ LS.valueRefs (fun v : ValueId => [v]) s mid := by
        simp [LS.valueRefs, live]
      have hbound := hrefs (.value s) hmem
      change s < mid.vals.size at hbound
      exact hbound
    · intro o ho
      simp [Op.origin] at ho
    · simp [Op.SymbolRefsValid]
  exact hrunAt.toSymbolRun

theorem lowerPlace_elem_symbolRun_of {le : LEnv} {scopeCount : Nat}
    {v : Core.View} {i : Core.Expr} {org : Core.OriginId}
    (hview : ∀ ls, LS.SymbolRun le scopeCount ls (fun x => [x]) (lowerView v))
    (hindex : ∀ ls, LS.SymbolRun le scopeCount ls (fun x => [x]) (lowerExpr i))
    (horg : org < le.mod.origins.size) :
    ∀ ls, LS.SymbolRun le scopeCount ls (fun x => [x]) (lowerPlace (.elem v i org)) := by
  intro ls
  have hrunAt : LS.SymbolRunAt le scopeCount ls (LS.valueRefs fun x => [x])
      (lowerPlace (.elem v i org)) := by
    change LS.SymbolRunAt le scopeCount ls (LS.valueRefs fun x => [x])
      (do let vw ← lowerView v
          let iv ← lowerExpr i
          emitDef (.indexChecked vw iv (some org)))
    apply LS.SymbolRunAt.bind ((hview ls).toSymbolRunAt (advB_lowerView v))
    intro vw mid hmid hcur hrefsView hadvView hdeadView
    apply LS.SymbolRunAt.bind ((hindex mid).toSymbolRunAt (advB_lowerExpr i))
    intro iv mid2 hmid2 hcur2 hrefsIndex hadvIndex hdeadIndex
    apply LS.SymbolRunAt.emitDef
    · intro live x hx
      simp [Op.uses] at hx
      rcases hx with hxvw | hxiv
      · subst x
        have hmidLive : mid.cur.isSome := by
          cases hcurMid : mid.cur with
          | none =>
            have hclosed := hdeadIndex hcurMid
            simp [hclosed] at live
          | some _ => simp
        have hmem : SymbolRef.value vw ∈ LS.valueRefs
            (fun x : ValueId => [x]) vw mid := by
          simp [LS.valueRefs, hmidLive]
        have hbound := hrefsView (.value vw) hmem
        change vw < mid.vals.size at hbound
        exact Nat.lt_of_lt_of_le hbound hadvIndex.vals
      · subst x
        have hmem : SymbolRef.value iv ∈ LS.valueRefs
            (fun x : ValueId => [x]) iv mid2 := by
          simp [LS.valueRefs, live]
        have hbound := hrefsIndex (.value iv) hmem
        change iv < mid2.vals.size at hbound
        exact hbound
    · intro o ho
      simp [Op.origin] at ho
      subst o
      exact horg
    · simp [Op.SymbolRefsValid]
  exact hrunAt.toSymbolRun

theorem lowerPlace_elem_symbolRun_of_tyPlace {le : LEnv} {scopeCount : Nat}
    {env : Core.TEnv} {v : Core.View} {i : Core.Expr} {org : Core.OriginId}
    {fuel : Nat} {info : Core.PlaceInfo} {fuel' : Nat}
    (hty : (Core.tyPlace env (.elem v i org)).run fuel = .ok (info, fuel'))
    (hview : ∀ ls, LS.SymbolRun le scopeCount ls (fun x => [x]) (lowerView v))
    (hindex : ∀ ls, LS.SymbolRun le scopeCount ls (fun x => [x]) (lowerExpr i))
    (horigins : le.mod.origins.size = env.mod.origins.size) :
    ∀ ls, LS.SymbolRun le scopeCount ls (fun x => [x]) (lowerPlace (.elem v i org)) := by
  apply lowerPlace_elem_symbolRun_of hview hindex
  rw [horigins]
  exact Core.tyPlace_elem_success_origin_bound hty

end Goose.Lower
