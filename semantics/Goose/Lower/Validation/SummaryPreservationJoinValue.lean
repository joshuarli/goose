import Goose.Lower.Validation.SummaryPreservationPatchBranches
import Goose.Lower.Validation.SummaryPreservationRefinedBlocks

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem joinValue_live_refined_witness {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {sourceRoots : List RootRef} {ls final : LS} {le : LEnv}
    {scopeCount : Nat} {value : ValueId} (live : List (BlockId × ValueId))
    (symbols : ls.SymbolWF le scopeCount)
    (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (bounds : ∀ pair ∈ live, pair.1 < ls.blocks.size ∧ pair.2 < ls.vals.size)
    (roots : ∀ pair ∈ live, RootsRefine func (rootsAt upper.vals pair.2) sourceRoots)
    (run : (do
      let ty ← valTy (live.headD (0, 0)).2
      let (join, params) ← newBlock [ty]
      patchBrs join live
      setCur (some join)
      pure (params.headD 0) : B ValueId) le ls = (value, final)) :
    ∃ next : Prov, BuilderRootWitness results vt func next final ∧
      BuilderEffectRefinement module vt func next source final ∧
      RootsRefine func (rootsAt next.vals value) sourceRoots ∧ next.slots = upper.slots ∧
      (∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) ∧
      rootsAt next.vals value = live.flatMap (fun pair => rootsAt upper.vals pair.2) ∧
      value < final.vals.size := by
  simp only [bind_eq] at run
  obtain ⟨ty, typeState, typeRun, ⟨join, params⟩, allocated, allocation,
    patchUnit, patched, patchRun, curUnit, selected, selecting, returned⟩ := run
  have same := valTy_eq typeRun
  subst typeState
  let seed := live.flatMap fun pair => rootsAt upper.vals pair.2
  have seedRefines : RootsRefine func seed sourceRoots := by
    intro root member
    obtain ⟨pair, member, rootMember⟩ := List.mem_flatMap.mp member
    exact roots pair member root rootMember
  obtain ⟨next, allocatedRoots, allocatedEffects, parameterRoots, slots, growth⟩ :=
    newBlock_parameter_refined_frame seed ty symbols witness prior
  rw [newBlock1_run] at allocation
  obtain ⟨pairEq, rfl⟩ := Prod.mk.inj allocation
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj pairEq
  have edgeRoots : ∀ pair ∈ live,
      EdgeRootsClosed { func with blocks := finishBlocks (ls.blocks.push ⟨[(ls.vals.size, ty)], #[]⟩) } next ls.blocks.size [pair.2] := by
    intro pair member target lookup entry entryMember root rootMember
    have targetEq : target = ⟨[(ls.vals.size, ty)], []⟩ := by
      simpa only [finishBlocks, Array.getElem?_map, Array.getElem?_push, ite_true, Option.map_some, Option.some.injEq] using lookup.symm
    subst target
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at entryMember
    subst entry
    rw [parameterRoots]
    apply List.mem_flatMap.mpr
    refine ⟨pair, member, ?_⟩
    rw [growth pair.2 (by simpa [witness.valueSize] using (bounds pair member).2)] at rootMember
    exact rootMember
  have patchedWitness := patchBrs_refined_witness live allocatedRoots allocatedEffects
    (fun pair member => by simpa only [newBlock1_run, Array.size_push] using Nat.lt_succ_of_lt (bounds pair member).1) edgeRoots patchRun
  rw [setCur_run] at selecting
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj selecting
  rw [pure_run] at returned
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj returned
  refine ⟨next, ⟨?_, patchedWitness.1.instructions⟩, patchedWitness.2.1, ?_, slots, growth,
    parameterRoots, ?_⟩
  · exact patchedWitness.1.valueSize
  · simpa [parameterRoots] using seedRefines
  · rw [patchedWitness.2.2.2.1]
    simp [newBlock1_run]


theorem joinValue_refined_witness {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {sourceRoots : List RootRef} {ls final : LS} {le : LEnv}
    {scopeCount : Nat} {value trueValue falseValue : ValueId} {trueEnd falseEnd : Option BlockId}
    (symbols : ls.SymbolWF le scopeCount)
    (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (trueBound : ∀ block, trueEnd = some block → block < ls.blocks.size ∧ trueValue < ls.vals.size)
    (falseBound : ∀ block, falseEnd = some block → block < ls.blocks.size ∧ falseValue < ls.vals.size)
    (trueRoots : trueEnd.isSome = true → RootsRefine func (rootsAt upper.vals trueValue) sourceRoots)
    (falseRoots : falseEnd.isSome = true → RootsRefine func (rootsAt upper.vals falseValue) sourceRoots)
    (run : joinValue trueEnd trueValue falseEnd falseValue le ls = (value, final)) :
    ∃ next : Prov, BuilderRootWitness results vt func next final ∧
      BuilderEffectRefinement module vt func next source final ∧
      (final.cur.isSome = true → RootsRefine func (rootsAt next.vals value) sourceRoots) ∧
      next.slots = upper.slots ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have key : ∀ live : List (BlockId × ValueId),
      (∀ pair ∈ live, pair.1 < ls.blocks.size ∧ pair.2 < ls.vals.size) →
      (∀ pair ∈ live, RootsRefine func (rootsAt upper.vals pair.2) sourceRoots) →
      (do
        let ty ← valTy (live.headD (0, 0)).2
        let (join, params) ← newBlock [ty]
        patchBrs join live
        setCur (some join)
        pure (params.headD 0) : B ValueId) le ls = (value, final) →
      ∃ next : Prov, BuilderRootWitness results vt func next final ∧
        BuilderEffectRefinement module vt func next source final ∧
        (final.cur.isSome = true → RootsRefine func (rootsAt next.vals value) sourceRoots) ∧
        next.slots = upper.slots ∧
        ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
    intro live bounds roots step
    obtain ⟨next, generated, effects, returned, slots, growth, _rawRoots, _bound⟩ :=
      joinValue_live_refined_witness live symbols witness prior bounds roots step
    exact ⟨next, generated, effects, fun _ => returned, slots, growth⟩
  unfold joinValue at run
  cases trueEnd with
  | none =>
    cases falseEnd with
    | none =>
      simp only [bind_run, setCur_run, pure_run] at run
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
      exact ⟨upper, ⟨witness.valueSize, witness.instructions⟩, prior, by simp, rfl, fun _ _ => rfl⟩
    | some block =>
      apply key _ (fun pair member => ?_) (fun pair member => ?_) run
      · simp at member
        subst pair
        exact falseBound block rfl
      · simp at member
        subst pair
        exact falseRoots rfl
  | some block =>
    cases falseEnd with
    | none =>
      apply key _ (fun pair member => ?_) (fun pair member => ?_) run
      · simp at member
        subst pair
        exact trueBound block rfl
      · simp at member
        subst pair
        exact trueRoots rfl
    | some other =>
      apply key _ (fun pair member => ?_) (fun pair member => ?_) run
      · simp at member
        rcases member with rfl | rfl
        · exact trueBound block rfl
        · exact falseBound other rfl
      · simp at member
        rcases member with rfl | rfl
        · exact trueRoots rfl
        · exact falseRoots rfl

end Goose.Lower.Validation.SummaryPreservation
