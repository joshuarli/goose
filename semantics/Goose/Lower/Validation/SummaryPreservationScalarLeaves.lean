import Goose.Lower.Validation.SummaryPreservationDefFrame

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerExpr_lit_refined_source_witness_growth {env : PEnv}
    {sourceRoots : List RootRef} {before after : RState} {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {ls : LS} {le : LEnv} {scopeCount : Nat} {block : BlockId} (ty : IntTy) (literal : Int)
    (replayed : rpExpr env (.lit ty literal) before = .ok (sourceRoots, after))
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper before.eff ls) :
    ∃ next : Prov,
      BuilderRootWitness results vt func next (lowerExpr (.lit ty literal) le ls).2 ∧
      BuilderEffectRefinement module vt func next after.eff (lowerExpr (.lit ty literal) le ls).2 ∧
      rootsAt next.vals (lowerExpr (.lit ty literal) le ls).1 = sourceRoots ∧
      next.slots = upper.slots ∧ (lowerExpr (.lit ty literal) le ls).2.SymbolWF le scopeCount ∧
      (lowerExpr (.lit ty literal) le ls).2.cur = some block ∧
      block < (lowerExpr (.lit ty literal) le ls).2.blocks.size ∧
      (lowerExpr (.lit ty literal) le ls).1 < (lowerExpr (.lit ty literal) le ls).2.vals.size ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  change (pure [] : P (List RootRef)) before = .ok (sourceRoots, after) at replayed
  have pair := (st_pure_ok _ _ _).mp replayed
  have sameRoots : sourceRoots = [] := congrArg Prod.fst pair
  have sameState : after = before := congrArg Prod.snd pair
  subst sourceRoots
  subst after
  obtain ⟨next, rootWitness, effects, returned, slots, nextSymbols, nextCurrent,
    nextBlockBound, nextValueBound, growth⟩ := emitDef_refined_frame_growth (.constInt ty literal) symbols current
      blockBound witness prior (by simp [Op.uses]) (by simp [Op.origin])
      (by simp [Op.SymbolRefsValid]) (effectRefinement_empty func before.eff)
  exact ⟨next, rootWitness, effects, returned, slots, nextSymbols, nextCurrent,
    nextBlockBound, nextValueBound, growth⟩

theorem lowerExpr_bool_refined_source_witness_growth {env : PEnv}
    {sourceRoots : List RootRef} {before after : RState} {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {ls : LS} {le : LEnv} {scopeCount : Nat} {block : BlockId} (literal : Bool)
    (replayed : rpExpr env (.bool literal) before = .ok (sourceRoots, after))
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper before.eff ls) :
    ∃ next : Prov,
      BuilderRootWitness results vt func next (lowerExpr (.bool literal) le ls).2 ∧
      BuilderEffectRefinement module vt func next after.eff (lowerExpr (.bool literal) le ls).2 ∧
      rootsAt next.vals (lowerExpr (.bool literal) le ls).1 = sourceRoots ∧
      next.slots = upper.slots ∧ (lowerExpr (.bool literal) le ls).2.SymbolWF le scopeCount ∧
      (lowerExpr (.bool literal) le ls).2.cur = some block ∧
      block < (lowerExpr (.bool literal) le ls).2.blocks.size ∧
      (lowerExpr (.bool literal) le ls).1 < (lowerExpr (.bool literal) le ls).2.vals.size ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  change (pure [] : P (List RootRef)) before = .ok (sourceRoots, after) at replayed
  have pair := (st_pure_ok _ _ _).mp replayed
  have sameRoots : sourceRoots = [] := congrArg Prod.fst pair
  have sameState : after = before := congrArg Prod.snd pair
  subst sourceRoots
  subst after
  obtain ⟨next, rootWitness, effects, returned, slots, nextSymbols, nextCurrent,
    nextBlockBound, nextValueBound, growth⟩ := emitDef_refined_frame_growth (.constBool literal) symbols current
      blockBound witness prior (by simp [Op.uses]) (by simp [Op.origin])
      (by simp [Op.SymbolRefsValid]) (effectRefinement_empty func before.eff)
  exact ⟨next, rootWitness, effects, returned, slots, nextSymbols, nextCurrent,
    nextBlockBound, nextValueBound, growth⟩

end Goose.Lower.Validation.SummaryPreservation
