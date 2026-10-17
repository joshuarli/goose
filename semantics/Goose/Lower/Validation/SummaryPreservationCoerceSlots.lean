import Goose.Lower.Validation.SummaryPreservationCoercions

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem coerceSlot_refined_witness_growth {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {sourceRoots : List RootRef} {ls : LS} {le : LEnv}
    {scopeCount : Nat} {block : BlockId} {value : ValueId} (slot : SlotId) (org : OriginId)
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (valueBound : value < ls.vals.size)
    (roots : RootsRefine func (rootsAt upper.vals value) sourceRoots)
    (originBound : org < le.mod.origins.size) :
    ∃ next : Prov, BuilderRootWitness results vt func next (coerceSlot slot value org le ls).2 ∧
      BuilderEffectRefinement module vt func next source (coerceSlot slot value org le ls).2 ∧
      RootsRefine func (rootsAt next.vals (coerceSlot slot value org le ls).1) sourceRoots ∧
      next.slots = upper.slots ∧ (coerceSlot slot value org le ls).2.SymbolWF le scopeCount ∧
      (coerceSlot slot value org le ls).2.cur = some block ∧
      block < (coerceSlot slot value org le ls).2.blocks.size ∧
      (coerceSlot slot value org le ls).1 < (coerceSlot slot value org le ls).2.vals.size ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  cases lookup : le.slots[slot]? with
  | none =>
    simp only [coerceSlot, bind_run, read_apply, lookup, pure_run]
    exact ⟨upper, witness, prior, roots, rfl, symbols, current, blockBound, valueBound, fun _ _ => rfl⟩
  | some destination =>
    simp only [coerceSlot, bind_run, read_apply, lookup]
    exact coerceTo_refined_witness_growth destination.ty org symbols current blockBound witness prior
      valueBound roots originBound


theorem coerceSlot_refined_witness {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {sourceRoots : List RootRef} {ls : LS} {le : LEnv}
    {scopeCount : Nat} {block : BlockId} {value : ValueId} (slot : SlotId) (org : OriginId)
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (valueBound : value < ls.vals.size)
    (roots : RootsRefine func (rootsAt upper.vals value) sourceRoots)
    (originBound : org < le.mod.origins.size) :
    ∃ next : Prov, BuilderRootWitness results vt func next (coerceSlot slot value org le ls).2 ∧
      BuilderEffectRefinement module vt func next source (coerceSlot slot value org le ls).2 ∧
      RootsRefine func (rootsAt next.vals (coerceSlot slot value org le ls).1) sourceRoots ∧
      next.slots = upper.slots ∧ (coerceSlot slot value org le ls).2.SymbolWF le scopeCount ∧
      (coerceSlot slot value org le ls).2.cur = some block ∧
      block < (coerceSlot slot value org le ls).2.blocks.size ∧
      (coerceSlot slot value org le ls).1 < (coerceSlot slot value org le ls).2.vals.size := by
  obtain ⟨next, rootWitness, effects, returned, slots, nextSymbols, nextCurrent,
    nextBlockBound, nextValueBound, _⟩ := coerceSlot_refined_witness_growth slot org symbols current
    blockBound witness prior valueBound roots originBound
  exact ⟨next, rootWitness, effects, returned, slots, nextSymbols, nextCurrent, nextBlockBound, nextValueBound⟩

theorem coerceResult_refined_witness_growth {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {sourceRoots : List RootRef} {ls : LS} {le : LEnv}
    {scopeCount : Nat} {block : BlockId} {value : ValueId} (org : OriginId)
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (valueBound : value < ls.vals.size)
    (roots : RootsRefine func (rootsAt upper.vals value) sourceRoots)
    (originBound : org < le.mod.origins.size) :
    ∃ next : Prov, BuilderRootWitness results vt func next (coerceResult value org le ls).2 ∧
      BuilderEffectRefinement module vt func next source (coerceResult value org le ls).2 ∧
      RootsRefine func (rootsAt next.vals (coerceResult value org le ls).1) sourceRoots ∧
      next.slots = upper.slots ∧ (coerceResult value org le ls).2.SymbolWF le scopeCount ∧
      (coerceResult value org le ls).2.cur = some block ∧
      block < (coerceResult value org le ls).2.blocks.size ∧
      (coerceResult value org le ls).1 < (coerceResult value org le ls).2.vals.size ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  cases lookup : le.results.head? with
  | none =>
    simp only [coerceResult, bind_run, read_apply, lookup, pure_run]
    exact ⟨upper, witness, prior, roots, rfl, symbols, current, blockBound, valueBound, fun _ _ => rfl⟩
  | some destination =>
    simp only [coerceResult, bind_run, read_apply, lookup]
    exact coerceTo_refined_witness_growth destination org symbols current blockBound witness prior
      valueBound roots originBound


theorem coerceResult_refined_witness {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {sourceRoots : List RootRef} {ls : LS} {le : LEnv}
    {scopeCount : Nat} {block : BlockId} {value : ValueId} (org : OriginId)
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (valueBound : value < ls.vals.size)
    (roots : RootsRefine func (rootsAt upper.vals value) sourceRoots)
    (originBound : org < le.mod.origins.size) :
    ∃ next : Prov, BuilderRootWitness results vt func next (coerceResult value org le ls).2 ∧
      BuilderEffectRefinement module vt func next source (coerceResult value org le ls).2 ∧
      RootsRefine func (rootsAt next.vals (coerceResult value org le ls).1) sourceRoots ∧
      next.slots = upper.slots ∧ (coerceResult value org le ls).2.SymbolWF le scopeCount ∧
      (coerceResult value org le ls).2.cur = some block ∧
      block < (coerceResult value org le ls).2.blocks.size ∧
      (coerceResult value org le ls).1 < (coerceResult value org le ls).2.vals.size := by
  obtain ⟨next, rootWitness, effects, returned, slots, nextSymbols, nextCurrent,
    nextBlockBound, nextValueBound, _⟩ := coerceResult_refined_witness_growth org symbols current
    blockBound witness prior valueBound roots originBound
  exact ⟨next, rootWitness, effects, returned, slots, nextSymbols, nextCurrent, nextBlockBound, nextValueBound⟩

end Goose.Lower.Validation.SummaryPreservation
