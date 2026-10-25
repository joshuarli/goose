import Goose.Lower.Validation.SummaryPreservationBorrowTo

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerExpr_ref_source_witness_growth {env : PEnv} {place : Place} {mutability : Mutability}
    {placeRoots sourceRoots : List RootRef} {initialSource before after : RState}
    {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {upper : Prov} {initial ls : LS} {le : LEnv}
    {scopeCount : Nat} {block : BlockId} {address : ValueId}
    (placeReplay : rpPlace env place initialSource = .ok (placeRoots, before))
    (source : rpExpr env (.ref mutability place) initialSource = .ok (sourceRoots, after))
    (placeRun : lowerPlace place le initial = (address, ls))
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper before.eff ls)
    (addressBound : address < ls.vals.size)
    (roots : RootsRefine func (rootsAt upper.vals address) placeRoots) :
    ∃ next : Prov,
      BuilderRootWitness results vt func next (lowerExpr (.ref mutability place) le initial).2 ∧
      BuilderEffectRefinement module vt func next after.eff
        (lowerExpr (.ref mutability place) le initial).2 ∧
      RootsRefine func (rootsAt next.vals (lowerExpr (.ref mutability place) le initial).1) sourceRoots ∧
      next.slots = upper.slots ∧ (lowerExpr (.ref mutability place) le initial).2.SymbolWF le scopeCount ∧
      (lowerExpr (.ref mutability place) le initial).2.cur = some block ∧
      block < (lowerExpr (.ref mutability place) le initial).2.blocks.size ∧
      (lowerExpr (.ref mutability place) le initial).1 <
        (lowerExpr (.ref mutability place) le initial).2.vals.size ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  change rpPlace env place initialSource = .ok (sourceRoots, after) at source
  rw [placeReplay] at source
  cases source
  have actual : lowerExpr (.ref mutability place) le initial = borrowTo mutability address le ls := by
    simp only [lowerExpr, bind_run, placeRun]
  rw [actual]
  exact borrowTo_refined_witness_growth mutability symbols current blockBound witness prior addressBound roots


theorem lowerExpr_ref_source_witness {env : PEnv} {place : Place} {mutability : Mutability}
    {placeRoots sourceRoots : List RootRef} {initialSource before after : RState}
    {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {upper : Prov} {initial ls : LS} {le : LEnv}
    {scopeCount : Nat} {block : BlockId} {address : ValueId}
    (placeReplay : rpPlace env place initialSource = .ok (placeRoots, before))
    (source : rpExpr env (.ref mutability place) initialSource = .ok (sourceRoots, after))
    (placeRun : lowerPlace place le initial = (address, ls))
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper before.eff ls)
    (addressBound : address < ls.vals.size)
    (roots : RootsRefine func (rootsAt upper.vals address) placeRoots) :
    ∃ next : Prov,
      BuilderRootWitness results vt func next (lowerExpr (.ref mutability place) le initial).2 ∧
      BuilderEffectRefinement module vt func next after.eff
        (lowerExpr (.ref mutability place) le initial).2 ∧
      RootsRefine func (rootsAt next.vals (lowerExpr (.ref mutability place) le initial).1) sourceRoots ∧
      next.slots = upper.slots ∧ (lowerExpr (.ref mutability place) le initial).2.SymbolWF le scopeCount ∧
      (lowerExpr (.ref mutability place) le initial).2.cur = some block ∧
      block < (lowerExpr (.ref mutability place) le initial).2.blocks.size ∧
      (lowerExpr (.ref mutability place) le initial).1 <
        (lowerExpr (.ref mutability place) le initial).2.vals.size := by
  obtain ⟨next, rootWitness, effects, returned, slots, nextSymbols, nextCurrent,
    nextBlockBound, nextValueBound, _⟩ := lowerExpr_ref_source_witness_growth placeReplay source placeRun symbols current blockBound witness prior addressBound roots
  exact ⟨next, rootWitness, effects, returned, slots, nextSymbols, nextCurrent, nextBlockBound, nextValueBound⟩


theorem lowerArg_byRef_refined_witness_growth {place : Place} {mutability : Mutability}
    {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {upper : Prov} {source : Core.Eff} {sourceRoots : List RootRef}
    {initial ls : LS} {le : LEnv} {scopeCount : Nat} {block : BlockId} {address : ValueId}
    (placeRun : lowerPlace place le initial = (address, ls))
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (addressBound : address < ls.vals.size)
    (roots : RootsRefine func (rootsAt upper.vals address) sourceRoots) :
    ∃ next : Prov,
      BuilderRootWitness results vt func next (lowerArg (.byRef mutability place) le initial).2 ∧
      BuilderEffectRefinement module vt func next source (lowerArg (.byRef mutability place) le initial).2 ∧
      RootsRefine func (rootsAt next.vals (lowerArg (.byRef mutability place) le initial).1) sourceRoots ∧
      next.slots = upper.slots ∧ (lowerArg (.byRef mutability place) le initial).2.SymbolWF le scopeCount ∧
      (lowerArg (.byRef mutability place) le initial).2.cur = some block ∧
      block < (lowerArg (.byRef mutability place) le initial).2.blocks.size ∧
      (lowerArg (.byRef mutability place) le initial).1 <
        (lowerArg (.byRef mutability place) le initial).2.vals.size ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have actual : lowerArg (.byRef mutability place) le initial = borrowTo mutability address le ls := by
    simp only [lowerArg, bind_run, placeRun]
  rw [actual]
  exact borrowTo_refined_witness_growth mutability symbols current blockBound witness prior addressBound roots


theorem lowerArg_byRef_refined_witness {place : Place} {mutability : Mutability}
    {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {upper : Prov} {source : Core.Eff} {sourceRoots : List RootRef}
    {initial ls : LS} {le : LEnv} {scopeCount : Nat} {block : BlockId} {address : ValueId}
    (placeRun : lowerPlace place le initial = (address, ls))
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (addressBound : address < ls.vals.size)
    (roots : RootsRefine func (rootsAt upper.vals address) sourceRoots) :
    ∃ next : Prov,
      BuilderRootWitness results vt func next (lowerArg (.byRef mutability place) le initial).2 ∧
      BuilderEffectRefinement module vt func next source (lowerArg (.byRef mutability place) le initial).2 ∧
      RootsRefine func (rootsAt next.vals (lowerArg (.byRef mutability place) le initial).1) sourceRoots ∧
      next.slots = upper.slots ∧ (lowerArg (.byRef mutability place) le initial).2.SymbolWF le scopeCount ∧
      (lowerArg (.byRef mutability place) le initial).2.cur = some block ∧
      block < (lowerArg (.byRef mutability place) le initial).2.blocks.size ∧
      (lowerArg (.byRef mutability place) le initial).1 <
        (lowerArg (.byRef mutability place) le initial).2.vals.size := by
  obtain ⟨next, rootWitness, effects, returned, slots, nextSymbols, nextCurrent,
    nextBlockBound, nextValueBound, _⟩ := lowerArg_byRef_refined_witness_growth placeRun symbols current blockBound witness prior addressBound roots
  exact ⟨next, rootWitness, effects, returned, slots, nextSymbols, nextCurrent, nextBlockBound, nextValueBound⟩

end Goose.Lower.Validation.SummaryPreservation
