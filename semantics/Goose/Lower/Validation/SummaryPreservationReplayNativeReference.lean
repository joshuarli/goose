import Goose.Lower.Validation.SummaryPreservationReplayReferences
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem typedReferenceNative {env : TEnv} {penv : PEnv} {mutability : Mutability} {place : Place}
    {type : Ty} {start finish : Nat} {before after : RState} {sourceRoots : List RootRef}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (source : Core.tyExpr env (.ref mutability place) start = .ok (type, finish))
    (replayed : rpExpr penv (.ref mutability place) before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerExpr (.ref mutability place) le ls).2)
    (child : ∀ info nextCounter,
      Core.tyPlace env place start = .ok (info, nextCounter) →
      rpPlace penv place before = .ok (sourceRoots, after) →
      EffectRefinement func after.eff target →
      GeneratedBuilderState ls → NativeRows vt (lowerPlace place le ls).2 →
      ∃ middle, ReplayBuilder module results vt func target le scopeCount slots (lowerPlace place le ls).2 middle ∧
        ((lowerPlace place le ls).2.cur.isSome = true →
          (lowerPlace place le ls).1 < (lowerPlace place le ls).2.vals.size ∧
          RootsRefine func (rootsAt middle.vals (lowerPlace place le ls).1) sourceRoots) ∧
        ∀ index, index < upper.vals.size → rootsAt middle.vals index = rootsAt upper.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.ref mutability place) le ls).2 next ∧
      ((lowerExpr (.ref mutability place) le ls).2.cur.isSome = true → ReplayValue func next
        (lowerExpr (.ref mutability place) le ls).2 (lowerExpr (.ref mutability place) le ls).1 sourceRoots (.data type)) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨info, nextCounter, typed, shape, _⟩ := tyExpr_ref_place source
  subst type
  have placeReplay : rpPlace penv place before = .ok (sourceRoots, after) := replayed
  let address := lowerPlace place le ls
  have placeNative := native.of_prefix (types_borrowTo mutability address.1 le address.2 _ _ rfl)
  obtain ⟨middle, middleReady, middleValue, middleRoots⟩ :=
    child info nextCounter typed placeReplay wholeEffect generated placeNative
  obtain ⟨next, nextReady, nextValue, nextRoots⟩ := middleReady.reference
    (targetTy := info.ty) placeReplay replayed (initial := ls) rfl middleValue
  refine ⟨next, nextReady, nextValue, ?_⟩
  intro index bound
  have growth : upper.vals.size ≤ middle.vals.size := by
    rw [ready.roots.valueSize, middleReady.roots.valueSize]
    exact (advB_lowerPlace place le ls address.1 address.2 rfl).vals
  exact (nextRoots index (Nat.lt_of_lt_of_le bound growth)).trans (middleRoots index bound)

#print axioms typedReferenceNative

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
