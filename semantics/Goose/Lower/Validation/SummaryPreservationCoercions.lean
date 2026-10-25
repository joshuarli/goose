import Goose.Lower.Validation.SummaryPreservationRelayGrowth

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem emitDef_relay_refined_witness {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {sourceRoots : List RootRef} {ls : LS} {le : LEnv}
    {scopeCount : Nat} {block : BlockId} {operand : ValueId} (op : Op)
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (roots : RootsRefine func (rootsAt upper.vals operand) sourceRoots)
    (uses : ∀ value ∈ op.uses, value < ls.vals.size)
    (origin : ∀ org, op.origin = some org → org < le.mod.origins.size)
    (references : Op.SymbolRefsValid le op)
    (relay : rootsOfDef results vt func upper ls.vals.size op = rootsAt upper.vals operand)
    (neutral : func.effectStep module vt upper {} (.def ls.vals.size op) = {}) :
    ∃ next : Prov, BuilderRootWitness results vt func next (emitDef op le ls).2 ∧
      BuilderEffectRefinement module vt func next source (emitDef op le ls).2 ∧
      RootsRefine func (rootsAt next.vals (emitDef op le ls).1) sourceRoots ∧ next.slots = upper.slots ∧
      (emitDef op le ls).2.SymbolWF le scopeCount ∧ (emitDef op le ls).2.cur = some block ∧
      block < (emitDef op le ls).2.blocks.size ∧ (emitDef op le ls).1 < (emitDef op le ls).2.vals.size := by
  obtain ⟨next, rootsWitness, effects, returned, slots, nextSymbols, nextCurrent,
    nextBlockBound, nextValueBound, _⟩ := emitDef_relay_refined_witness_growth op symbols current
    blockBound witness prior roots uses origin references relay neutral
  exact ⟨next, rootsWitness, effects, returned, slots, nextSymbols, nextCurrent, nextBlockBound, nextValueBound⟩

private theorem coerceTo_run_cases (target : Ty) (value : ValueId) (org : OriginId)
    (le : LEnv) (ls : LS) :
    coerceTo target value org le ls = (value, ls) ∨
    coerceTo target value org le ls = emitDef (.refFreeze value) le ls ∨
    coerceTo target value org le ls =
      let view := emitDef (.sliceView value) le ls
      emitDef (.viewSlice .readOnly view.1 .omitted .omitted (some org)) le view.2 := by
  simp only [coerceTo, bind_run, valTy_run]
  generalize valueTypeRow : (valTy value le ls).1 = valueType
  cases target <;> cases valueType <;> try exact Or.inl rfl
  case ref.data targetMutability target actualType =>
    cases targetMutability <;> cases actualType <;> try exact Or.inl rfl
    rename_i actualMutability actualTarget
    cases actualMutability <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
  case ref.view targetMutability target viewMutability element =>
    cases targetMutability <;> exact Or.inl rfl
  case slice.view targetMutability element viewMutability viewElement =>
    cases targetMutability <;> exact Or.inl rfl
  case slice.data targetMutability element actualType =>
    cases targetMutability <;> cases actualType <;> try exact Or.inl rfl
    rename_i actualMutability actualElement
    cases actualMutability <;> first | exact Or.inl rfl | exact Or.inr (Or.inr rfl)


theorem coerceTo_refined_witness_growth {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {sourceRoots : List RootRef} {ls : LS} {le : LEnv}
    {scopeCount : Nat} {block : BlockId} {value : ValueId} (target : Ty) (org : OriginId)
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (valueBound : value < ls.vals.size)
    (roots : RootsRefine func (rootsAt upper.vals value) sourceRoots)
    (originBound : org < le.mod.origins.size) :
    ∃ next : Prov, BuilderRootWitness results vt func next (coerceTo target value org le ls).2 ∧
      BuilderEffectRefinement module vt func next source (coerceTo target value org le ls).2 ∧
      RootsRefine func (rootsAt next.vals (coerceTo target value org le ls).1) sourceRoots ∧
      next.slots = upper.slots ∧ (coerceTo target value org le ls).2.SymbolWF le scopeCount ∧
      (coerceTo target value org le ls).2.cur = some block ∧
      block < (coerceTo target value org le ls).2.blocks.size ∧
      (coerceTo target value org le ls).1 < (coerceTo target value org le ls).2.vals.size ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  rcases coerceTo_run_cases target value org le ls with same | freeze | slice
  · rw [same]
    exact ⟨upper, witness, prior, roots, rfl, symbols, current, blockBound, valueBound, fun _ _ => rfl⟩
  · rw [freeze]
    exact emitDef_relay_refined_witness_growth (.refFreeze value) symbols current blockBound witness prior roots
      (by simpa [Op.uses] using valueBound) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid]) rfl rfl
  · rw [slice]
    obtain ⟨middle, middleWitness, middleEffects, middleRoots, middleSlots, middleSymbols,
      middleCurrent, middleBlockBound, middleValueBound, middleGrowth⟩ :=
      emitDef_relay_refined_witness_growth (.sliceView value) symbols current blockBound witness prior roots
        (by simpa [Op.uses] using valueBound) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid]) rfl rfl
    obtain ⟨next, nextWitness, nextEffects, nextRoots, nextSlots, nextSymbols,
      nextCurrent, nextBlockBound, nextValueBound, nextGrowth⟩ :=
      emitDef_relay_refined_witness_growth
        (.viewSlice .readOnly (emitDef (.sliceView value) le ls).1 .omitted .omitted (some org))
        middleSymbols middleCurrent middleBlockBound middleWitness middleEffects middleRoots
        (by simpa [Op.uses, Bnd.uses] using middleValueBound)
        (by simpa [Op.origin] using originBound) (by simp [Op.SymbolRefsValid]) rfl rfl
    refine ⟨next, nextWitness, nextEffects, nextRoots, nextSlots.trans middleSlots,
      nextSymbols, nextCurrent, nextBlockBound, nextValueBound, ?_⟩
    intro index bound
    have intermediate : index < middle.vals.size := by
      rw [middleWitness.valueSize, emitDef_run _ _ current]
      simp only [Array.size_push]
      rw [← witness.valueSize]
      exact Nat.lt_succ_of_lt bound
    exact (nextGrowth index intermediate).trans (middleGrowth index bound)

theorem coerceTo_refined_witness {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {sourceRoots : List RootRef} {ls : LS} {le : LEnv}
    {scopeCount : Nat} {block : BlockId} {value : ValueId} (target : Ty) (org : OriginId)
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (valueBound : value < ls.vals.size)
    (roots : RootsRefine func (rootsAt upper.vals value) sourceRoots)
    (originBound : org < le.mod.origins.size) :
    ∃ next : Prov, BuilderRootWitness results vt func next (coerceTo target value org le ls).2 ∧
      BuilderEffectRefinement module vt func next source (coerceTo target value org le ls).2 ∧
      RootsRefine func (rootsAt next.vals (coerceTo target value org le ls).1) sourceRoots ∧
      next.slots = upper.slots ∧ (coerceTo target value org le ls).2.SymbolWF le scopeCount ∧
      (coerceTo target value org le ls).2.cur = some block ∧
      block < (coerceTo target value org le ls).2.blocks.size ∧
      (coerceTo target value org le ls).1 < (coerceTo target value org le ls).2.vals.size := by
  obtain ⟨next, rootsWitness, effects, returned, slots, nextSymbols, nextCurrent,
    nextBlockBound, nextValueBound, _⟩ := coerceTo_refined_witness_growth target org symbols current
    blockBound witness prior valueBound roots originBound
  exact ⟨next, rootsWitness, effects, returned, slots, nextSymbols, nextCurrent, nextBlockBound, nextValueBound⟩

end Goose.Lower.Validation.SummaryPreservation
