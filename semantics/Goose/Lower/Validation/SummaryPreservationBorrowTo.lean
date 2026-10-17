import Goose.Lower.Validation.SummaryPreservationCoercions

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

private theorem freezeTo_run_cases (mutability : Mutability) (value : ValueId) (le : LEnv) (ls : LS) :
    freezeTo mutability value le ls = (value, ls) ∨
      freezeTo mutability value le ls = emitDef (.refFreeze value) le ls := by
  simp only [freezeTo, bind_run, valTy_run]
  generalize valueTypeRow : (valTy value le ls).1 = valueType
  cases mutability <;> cases valueType <;> try exact Or.inl rfl
  case readOnly.data actualType =>
    cases actualType <;> try exact Or.inl rfl
    rename_i actualMutability actualTarget
    cases actualMutability <;> first | exact Or.inl rfl | exact Or.inr rfl


theorem freezeTo_refined_witness_growth {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {sourceRoots : List RootRef} {ls : LS} {le : LEnv}
    {scopeCount : Nat} {block : BlockId} {value : ValueId} (mutability : Mutability)
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (valueBound : value < ls.vals.size)
    (roots : RootsRefine func (rootsAt upper.vals value) sourceRoots) :
    ∃ next : Prov, BuilderRootWitness results vt func next (freezeTo mutability value le ls).2 ∧
      BuilderEffectRefinement module vt func next source (freezeTo mutability value le ls).2 ∧
      RootsRefine func (rootsAt next.vals (freezeTo mutability value le ls).1) sourceRoots ∧
      next.slots = upper.slots ∧ (freezeTo mutability value le ls).2.SymbolWF le scopeCount ∧
      (freezeTo mutability value le ls).2.cur = some block ∧
      block < (freezeTo mutability value le ls).2.blocks.size ∧
      (freezeTo mutability value le ls).1 < (freezeTo mutability value le ls).2.vals.size ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  rcases freezeTo_run_cases mutability value le ls with same | freeze
  · rw [same]
    exact ⟨upper, witness, prior, roots, rfl, symbols, current, blockBound, valueBound, fun _ _ => rfl⟩
  · rw [freeze]
    exact emitDef_relay_refined_witness_growth (.refFreeze value) symbols current blockBound witness prior roots
      (by simpa [Op.uses] using valueBound) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid]) rfl rfl


theorem freezeTo_refined_witness {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {sourceRoots : List RootRef} {ls : LS} {le : LEnv}
    {scopeCount : Nat} {block : BlockId} {value : ValueId} (mutability : Mutability)
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (valueBound : value < ls.vals.size)
    (roots : RootsRefine func (rootsAt upper.vals value) sourceRoots) :
    ∃ next : Prov, BuilderRootWitness results vt func next (freezeTo mutability value le ls).2 ∧
      BuilderEffectRefinement module vt func next source (freezeTo mutability value le ls).2 ∧
      RootsRefine func (rootsAt next.vals (freezeTo mutability value le ls).1) sourceRoots ∧
      next.slots = upper.slots ∧ (freezeTo mutability value le ls).2.SymbolWF le scopeCount ∧
      (freezeTo mutability value le ls).2.cur = some block ∧
      block < (freezeTo mutability value le ls).2.blocks.size ∧
      (freezeTo mutability value le ls).1 < (freezeTo mutability value le ls).2.vals.size := by
  obtain ⟨next, rootWitness, effects, returned, slots, nextSymbols, nextCurrent,
    nextBlockBound, nextValueBound, _⟩ := freezeTo_refined_witness_growth mutability symbols current
    blockBound witness prior valueBound roots
  exact ⟨next, rootWitness, effects, returned, slots, nextSymbols, nextCurrent, nextBlockBound, nextValueBound⟩

private theorem borrowTo_run_cases (mutability : Mutability) (value : ValueId) (le : LEnv) (ls : LS) :
    borrowTo mutability value le ls = emitDef (.ownerBorrow value) le ls ∨
      borrowTo mutability value le ls = freezeTo mutability value le ls := by
  let owner := match (valTy value le ls).1 with
    | .data (.ref .mutable (.grow _)) | .data (.ref .mutable (.growshrink _)) => true
    | _ => false
  by_cases chosen : (mutability == .mutable && le.mod.profile == .shrink && owner) = true
  · left
    simp only [borrowTo, bind_run, read_apply, valTy_run]
    change (if mutability == .mutable && le.mod.profile == .shrink && owner then
      emitDef (.ownerBorrow value) else freezeTo mutability value) le ls = _
    simp only [chosen, ite_true]
  · right
    simp only [borrowTo, bind_run, read_apply, valTy_run]
    change (if mutability == .mutable && le.mod.profile == .shrink && owner then
      emitDef (.ownerBorrow value) else freezeTo mutability value) le ls = _
    simp only [chosen, Bool.false_eq_true, ite_false]


theorem borrowTo_refined_witness_growth {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {sourceRoots : List RootRef} {ls : LS} {le : LEnv}
    {scopeCount : Nat} {block : BlockId} {value : ValueId} (mutability : Mutability)
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (valueBound : value < ls.vals.size)
    (roots : RootsRefine func (rootsAt upper.vals value) sourceRoots) :
    ∃ next : Prov, BuilderRootWitness results vt func next (borrowTo mutability value le ls).2 ∧
      BuilderEffectRefinement module vt func next source (borrowTo mutability value le ls).2 ∧
      RootsRefine func (rootsAt next.vals (borrowTo mutability value le ls).1) sourceRoots ∧
      next.slots = upper.slots ∧ (borrowTo mutability value le ls).2.SymbolWF le scopeCount ∧
      (borrowTo mutability value le ls).2.cur = some block ∧
      block < (borrowTo mutability value le ls).2.blocks.size ∧
      (borrowTo mutability value le ls).1 < (borrowTo mutability value le ls).2.vals.size ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  rcases borrowTo_run_cases mutability value le ls with borrow | freeze
  · rw [borrow]
    exact emitDef_relay_refined_witness_growth (.ownerBorrow value) symbols current blockBound witness prior roots
      (by simpa [Op.uses] using valueBound) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid]) rfl rfl
  · rw [freeze]
    exact freezeTo_refined_witness_growth mutability symbols current blockBound witness prior valueBound roots

theorem borrowTo_refined_witness {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {sourceRoots : List RootRef} {ls : LS} {le : LEnv}
    {scopeCount : Nat} {block : BlockId} {value : ValueId} (mutability : Mutability)
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (valueBound : value < ls.vals.size)
    (roots : RootsRefine func (rootsAt upper.vals value) sourceRoots) :
    ∃ next : Prov, BuilderRootWitness results vt func next (borrowTo mutability value le ls).2 ∧
      BuilderEffectRefinement module vt func next source (borrowTo mutability value le ls).2 ∧
      RootsRefine func (rootsAt next.vals (borrowTo mutability value le ls).1) sourceRoots ∧
      next.slots = upper.slots ∧ (borrowTo mutability value le ls).2.SymbolWF le scopeCount ∧
      (borrowTo mutability value le ls).2.cur = some block ∧
      block < (borrowTo mutability value le ls).2.blocks.size ∧
      (borrowTo mutability value le ls).1 < (borrowTo mutability value le ls).2.vals.size := by
  obtain ⟨next, rootWitness, effects, returned, slots, nextSymbols, nextCurrent,
    nextBlockBound, nextValueBound, _⟩ := borrowTo_refined_witness_growth mutability symbols current
    blockBound witness prior valueBound roots
  exact ⟨next, rootWitness, effects, returned, slots, nextSymbols, nextCurrent, nextBlockBound, nextValueBound⟩

end Goose.Lower.Validation.SummaryPreservation
