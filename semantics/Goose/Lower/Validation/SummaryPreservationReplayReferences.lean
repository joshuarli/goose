import Goose.Lower.Validation.SummaryPreservationReplayValue
import Goose.Lower.Validation.SummaryPreservationReplayStopped
import Goose.Lower.Validation.SummaryPreservationBorrowTo

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem borrowReference (mutability : Mutability) (targetTy : Ty) (address : ValueId)
    (sourceRoots : List RootRef)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (input : ls.cur.isSome = true → address < ls.vals.size ∧
      RootsRefine func (rootsAt upper.vals address) sourceRoots) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (borrowTo mutability address le ls).2 next ∧
      ((borrowTo mutability address le ls).2.cur.isSome = true →
        ReplayValue func next (borrowTo mutability address le ls).2
          (borrowTo mutability address le ls).1 sourceRoots (.data (.ref mutability targetTy))) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  cases current : ls.cur with
  | none =>
    have stable := stopped_borrowTo mutability address
    have generated : ReplayBuilder module results vt func target le scopeCount slots
        (borrowTo mutability address le ls).2 upper := ready.stopped stable current rfl
    have dead : (borrowTo mutability address le ls).2.cur = none :=
      (stable le ls (borrowTo mutability address le ls).1 (borrowTo mutability address le ls).2 rfl current).1
    exact ⟨upper, generated, by simp [dead], fun _ _ => rfl⟩
  | some block =>
    obtain ⟨bound, refined⟩ := input (by simp [current])
    obtain ⟨next, nextRoots, effects, returned, nextSlots, symbols, nextCurrent,
      blockBound, valueBound, growth⟩ := borrowTo_refined_witness_growth mutability ready.symbols current
        (ready.current block current) ready.roots ready.effects bound refined
    refine ⟨next, ⟨nextRoots, effects, symbols, ?_, nextSlots.trans ready.slotsEq,
      ready.recipes.prefix (recipesUnchangedB_borrowTo mutability address le ls) growth (by
        rw [ready.roots.valueSize, nextRoots.valueSize]
        exact (advB_borrowTo mutability address le ls _ _ rfl).vals)⟩, ?_, growth⟩
    · intro candidate candidateRow
      rw [nextCurrent] at candidateRow
      cases candidateRow
      exact blockBound
    · intro _
      exact ⟨valueBound, returned, by simp [VTy.refLike, Ty.isRefLike]⟩

theorem reference {env : PEnv} {place : Place} {mutability : Mutability} {targetTy : Ty}
    {initialSource before after : RState} {placeRoots sourceRoots : List RootRef}
    {initial : LS} {address : ValueId}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (placeReplay : rpPlace env place initialSource = .ok (placeRoots, before))
    (source : rpExpr env (.ref mutability place) initialSource = .ok (sourceRoots, after))
    (placeRun : lowerPlace place le initial = (address, ls))
    (input : ls.cur.isSome = true → address < ls.vals.size ∧
      RootsRefine func (rootsAt upper.vals address) placeRoots) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.ref mutability place) le initial).2 next ∧
      ((lowerExpr (.ref mutability place) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.ref mutability place) le initial).2
          (lowerExpr (.ref mutability place) le initial).1 sourceRoots (.data (.ref mutability targetTy))) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  change rpPlace env place initialSource = .ok (sourceRoots, after) at source
  rw [placeReplay] at source
  cases source
  have whole : lowerExpr (.ref mutability place) le initial = borrowTo mutability address le ls := by
    simp only [lowerExpr, bind_run, placeRun]
  rw [whole]
  exact ready.borrowReference mutability targetTy address placeRoots input

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
