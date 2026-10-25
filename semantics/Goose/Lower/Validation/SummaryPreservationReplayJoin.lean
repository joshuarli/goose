import Goose.Lower.Validation.SourceCanonicalRootFloorsRecipesJoin
import Goose.Lower.Validation.SummaryPreservationRefinedResults
import Goose.Lower.Validation.SummaryPreservationReplayValue
import Goose.Lower.Validation.SummaryPreservationJoinValue

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem patchBrs_symbols {ls final : LS} {le : LEnv} {scopeCount : Nat}
    {destination : BlockId} {resultUnit : Unit} (edges : List (BlockId × ValueId))
    (symbols : ls.SymbolWF le scopeCount) (destinationBound : destination < ls.blocks.size)
    (bounds : ∀ pair ∈ edges, pair.1 < ls.blocks.size ∧ pair.2 < ls.vals.size)
    (run : patchBrs destination edges le ls = (resultUnit, final)) :
    final.SymbolWF le scopeCount ∧ final.cur = ls.cur := by
  induction edges generalizing ls final with
  | nil =>
    change ((), ls) = (resultUnit, final) at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    exact ⟨symbols, rfl⟩
  | cons pair rest ih =>
    obtain ⟨_, middle, first, tail⟩ := bind_eq.mp run
    rw [patchTerm_run] at first
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj first
    have generated := symbols.patchTerm (bounds pair (by simp)).1 (t := .br destination [pair.2]) (by
      apply Inst.SymbolsWithin.term
      · simpa [Term.uses] using (bounds pair (by simp)).2
      · simp [Term.origin]
      · simpa [Term.successors] using destinationBound)
    exact ih (ls := { ls with blocks := ls.blocks.modify pair.1 fun blk =>
      { blk with insts := blk.insts.push (.term (.br destination [pair.2])) } })
      generated (by simpa using destinationBound)
      (fun next member => by simpa using bounds next (by simp [member])) tail

namespace ReplayBuilder

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls final : LS} {upper : Prov}

theorem liveJoinWithCeiling (live : List (BlockId × ValueId)) {value : ValueId}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (sourceRoots : List RootRef) (type : VTy)
    (bounds : ∀ pair ∈ live, pair.1 < ls.blocks.size ∧ pair.2 < ls.vals.size)
    (roots : ∀ pair ∈ live, RootsRefine func (rootsAt upper.vals pair.2) sourceRoots)
    (scalar : type.refLike = false → ∀ pair ∈ live, rootsAt upper.vals pair.2 = [])
    (run : (do
      let ty ← valTy (live.headD (0, 0)).2
      let (join, params) ← newBlock [ty]
      patchBrs join live
      Goose.Lower.setCur (some join)
      pure (params.headD 0) : B ValueId) le ls = (value, final)) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots final next ∧
      ReplayValue func next final value sourceRoots type ∧
      (∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) ∧
      (type.refLike = true → refinedResultUpper func sourceRoots ⊆ rootsAt next.vals value) := by
  let original := live.flatMap fun pair => rootsAt upper.vals pair.2
  let ceiling := if type.refLike then refinedResultUpper func sourceRoots else []
  have originalRefines : RootsRefine func original sourceRoots := by
    intro root member
    obtain ⟨pair, member, rootMember⟩ := List.mem_flatMap.mp member
    exact roots pair member root rootMember
  have ceilingRefines : RootsRefine func ceiling sourceRoots := by
    dsimp [ceiling]
    split
    · exact refinedResultUpper_refines _ _
    · exact RootsRefine.empty _ _
  obtain ⟨next, generatedRoots, effects, refined, slotRoots, growth, exactRoots, valueBound⟩ :=
    joinValue_live_seeded_witness live ready.symbols ready.roots ready.effects bounds
      (unionRoots original ceiling) (originalRefines.union ceilingRefines)
      (fun pair member root rootMember => unionRoots_left _ _ _
        (List.mem_flatMap.mpr ⟨pair, member, rootMember⟩)) run
  have containsCeiling : type.refLike = true → refinedResultUpper func sourceRoots ⊆ rootsAt next.vals value := by
    intro reference root member
    rw [exactRoots]
    exact unionRoots_right _ _ root (by simpa [ceiling, reference] using member)
  have valueReady : ReplayValue func next final value sourceRoots type := by
    refine ⟨valueBound, refined, ?_⟩
    intro nonref
    rw [exactRoots]
    have empty : original = [] := List.flatMap_eq_nil_iff.mpr (scalar nonref)
    simp [empty, ceiling, nonref, unionRoots]
  simp only [bind_eq] at run
  obtain ⟨ty, typeState, typeRun, ⟨join, params⟩, allocated, allocation,
    patchUnit, patched, patchRun, curUnit, selected, selecting, returned⟩ := run
  have same := valTy_eq typeRun
  subst typeState
  have allocatedSymbols : allocated.SymbolWF le scopeCount := by
    have symbols := ready.symbols.newBlock (tys := [ty])
    rw [newBlock1_run] at allocation
    cases allocation
    simpa [paramIds, pushParamTypes] using symbols
  have destinationBound : join < allocated.blocks.size := by
    rw [newBlock1_run] at allocation
    cases allocation
    simp
  have allocatedBounds : ∀ pair ∈ live, pair.1 < allocated.blocks.size ∧ pair.2 < allocated.vals.size := by
    rw [newBlock1_run] at allocation
    cases allocation
    intro pair member
    simpa using And.intro (Nat.lt_succ_of_lt (bounds pair member).1)
      (Nat.lt_succ_of_lt (bounds pair member).2)
  have patchedSymbols := (patchBrs_symbols live allocatedSymbols destinationBound allocatedBounds patchRun).1
  have blockSize := patchBrs_size live patchRun
  rw [setCur_run] at selecting
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj selecting
  rw [pure_run] at returned
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj returned
  refine ⟨next, ⟨generatedRoots, effects, patchedSymbols.changeCur _, ?_, slotRoots.trans ready.slotsEq,
      ready.recipes.prefix (by
        have same := recipesUnchangedB_patchBrs join live le allocated
        rw [patchRun] at same
        have allocatedRecipes : allocated.valueRootRecipes = ls.valueRootRecipes := by
          rw [newBlock1_run] at allocation
          cases allocation
          rfl
        exact same.trans allocatedRecipes) growth (by
        rw [ready.roots.valueSize, generatedRoots.valueSize]
        have unchanged := SourceCanonicalRootFloors.patchBrs_vals join live le allocated
        rw [patchRun] at unchanged
        change ls.vals.size ≤ patched.vals.size
        rw [unchanged]
        exact (advB_newBlock1 ty le ls _ _ allocation).vals)⟩,
    valueReady, growth, containsCeiling⟩
  intro block row
  simp only [Option.some.injEq] at row
  subst block
  exact blockSize ▸ destinationBound

theorem liveJoin (live : List (BlockId × ValueId)) {value : ValueId}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (sourceRoots : List RootRef) (type : VTy)
    (bounds : ∀ pair ∈ live, pair.1 < ls.blocks.size ∧ pair.2 < ls.vals.size)
    (roots : ∀ pair ∈ live, RootsRefine func (rootsAt upper.vals pair.2) sourceRoots)
    (scalar : type.refLike = false → ∀ pair ∈ live, rootsAt upper.vals pair.2 = [])
    (run : (do
      let ty ← valTy (live.headD (0, 0)).2
      let (join, params) ← newBlock [ty]
      patchBrs join live
      Goose.Lower.setCur (some join)
      pure (params.headD 0) : B ValueId) le ls = (value, final)) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots final next ∧
      ReplayValue func next final value sourceRoots type ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨next, nextReady, nextValue, retained, _ceiling⟩ :=
    ready.liveJoinWithCeiling live sourceRoots type bounds roots scalar run
  exact ⟨next, nextReady, nextValue, retained⟩

theorem joinValueWithCeiling {value trueValue falseValue : ValueId} {trueEnd falseEnd : Option BlockId}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (sourceRoots : List RootRef) (type : VTy)
    (trueBound : ∀ block, trueEnd = some block → block < ls.blocks.size ∧ trueValue < ls.vals.size)
    (falseBound : ∀ block, falseEnd = some block → block < ls.blocks.size ∧ falseValue < ls.vals.size)
    (trueRoots : trueEnd.isSome = true → RootsRefine func (rootsAt upper.vals trueValue) sourceRoots)
    (falseRoots : falseEnd.isSome = true → RootsRefine func (rootsAt upper.vals falseValue) sourceRoots)
    (trueScalar : type.refLike = false → trueEnd.isSome = true → rootsAt upper.vals trueValue = [])
    (falseScalar : type.refLike = false → falseEnd.isSome = true → rootsAt upper.vals falseValue = [])
    (run : Goose.Lower.joinValue trueEnd trueValue falseEnd falseValue le ls = (value, final)) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots final next ∧
      (final.cur.isSome = true → ReplayValue func next final value sourceRoots type) ∧
      (∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) ∧
      (type.refLike = true → final.cur.isSome = true →
        refinedResultUpper func sourceRoots ⊆ rootsAt next.vals value) := by
  have key (live : List (BlockId × ValueId))
      (bounds : ∀ pair ∈ live, pair.1 < ls.blocks.size ∧ pair.2 < ls.vals.size)
      (roots : ∀ pair ∈ live, RootsRefine func (rootsAt upper.vals pair.2) sourceRoots)
      (scalar : type.refLike = false → ∀ pair ∈ live, rootsAt upper.vals pair.2 = [])
      (step : (do
        let ty ← valTy (live.headD (0, 0)).2
        let (join, params) ← newBlock [ty]
        patchBrs join live
        Goose.Lower.setCur (some join)
        pure (params.headD 0) : B ValueId) le ls = (value, final)) :
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots final next ∧
        (final.cur.isSome = true → ReplayValue func next final value sourceRoots type) ∧
        (∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) ∧
      (type.refLike = true → final.cur.isSome = true →
        refinedResultUpper func sourceRoots ⊆ rootsAt next.vals value) := by
    obtain ⟨next, generated, returned, retained, included⟩ :=
      ready.liveJoinWithCeiling live sourceRoots type bounds roots scalar step
    exact ⟨next, generated, fun _ => returned, retained, fun reference _ => included reference⟩
  unfold Goose.Lower.joinValue at run
  cases trueEnd with
  | none =>
    cases falseEnd with
    | none =>
      simp only [bind_run, setCur_run, pure_run] at run
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
      exact ⟨upper, ready.setCur none (by simp), by simp, (fun _ _ => rfl), by simp⟩
    | some block =>
      apply key _ (fun pair member => ?_) (fun pair member => ?_) (fun nonref pair member => ?_) run
      · simp at member; subst pair; exact falseBound block rfl
      · simp at member; subst pair; exact falseRoots rfl
      · simp at member; subst pair; exact falseScalar nonref rfl
  | some block =>
    cases falseEnd with
    | none =>
      apply key _ (fun pair member => ?_) (fun pair member => ?_) (fun nonref pair member => ?_) run
      · simp at member; subst pair; exact trueBound block rfl
      · simp at member; subst pair; exact trueRoots rfl
      · simp at member; subst pair; exact trueScalar nonref rfl
    | some other =>
      apply key _ (fun pair member => ?_) (fun pair member => ?_) (fun nonref pair member => ?_) run
      · simp at member
        rcases member with rfl | rfl
        · exact trueBound block rfl
        · exact falseBound other rfl
      · simp at member
        rcases member with rfl | rfl
        · exact trueRoots rfl
        · exact falseRoots rfl
      · simp at member
        rcases member with rfl | rfl
        · exact trueScalar nonref rfl
        · exact falseScalar nonref rfl

theorem joinValue {value trueValue falseValue : ValueId} {trueEnd falseEnd : Option BlockId}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (sourceRoots : List RootRef) (type : VTy)
    (trueBound : ∀ block, trueEnd = some block → block < ls.blocks.size ∧ trueValue < ls.vals.size)
    (falseBound : ∀ block, falseEnd = some block → block < ls.blocks.size ∧ falseValue < ls.vals.size)
    (trueRoots : trueEnd.isSome = true → RootsRefine func (rootsAt upper.vals trueValue) sourceRoots)
    (falseRoots : falseEnd.isSome = true → RootsRefine func (rootsAt upper.vals falseValue) sourceRoots)
    (trueScalar : type.refLike = false → trueEnd.isSome = true → rootsAt upper.vals trueValue = [])
    (falseScalar : type.refLike = false → falseEnd.isSome = true → rootsAt upper.vals falseValue = [])
    (run : Goose.Lower.joinValue trueEnd trueValue falseEnd falseValue le ls = (value, final)) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots final next ∧
      (final.cur.isSome = true → ReplayValue func next final value sourceRoots type) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨next, nextReady, nextValue, retained, _ceiling⟩ :=
    ready.joinValueWithCeiling sourceRoots type trueBound falseBound trueRoots falseRoots
      trueScalar falseScalar run
  exact ⟨next, nextReady, nextValue, retained⟩

end ReplayBuilder

end Goose.Lower.Validation.SummaryPreservation
