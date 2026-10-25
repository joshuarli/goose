import Goose.Lower.Validation.SummaryPreservationReplayNativeUnary
import Goose.Lower.Validation.SummaryPreservationReplayCompare

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem typedBinaryNative {env : TEnv} {penv : PEnv} {op : BinOp} {left right : Expr} {origin : OriginId}
    {type : Ty} {start finish : Nat} {before after : RState} {sourceRoots : List RootRef}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (source : Core.tyExpr env (.bin op left right origin) start = .ok (type, finish))
    (replayed : rpExpr penv (.bin op left right origin) before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (originBound : origin < le.mod.origins.size)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerExpr (.bin op left right origin) le ls).2)
    (leftChild : ∀ childStart childFinish integer roots sourceAfter,
      Core.tyExpr env left childStart = .ok (.int integer, childFinish) →
      rpExpr penv left before = .ok (roots, sourceAfter) →
      EffectRefinement func sourceAfter.eff target →
      GeneratedBuilderState ls → NativeRows vt (lowerExpr left le ls).2 →
      ∃ middle, ReplayBuilder module results vt func target le scopeCount slots (lowerExpr left le ls).2 middle ∧
        ((lowerExpr left le ls).2.cur.isSome = true → ReplayValue func middle
          (lowerExpr left le ls).2 (lowerExpr left le ls).1 roots (.data (.int integer))) ∧
        ∀ index, index < upper.vals.size → rootsAt middle.vals index = rootsAt upper.vals index)
    (rightChild : ∀ childStart childFinish integer sourceBefore roots sourceAfter provenance,
      Core.tyExpr env right childStart = .ok (.int integer, childFinish) →
      rpExpr penv right sourceBefore = .ok (roots, sourceAfter) →
      EffectRefinement func sourceAfter.eff target →
      ReplayBuilder module results vt func target le scopeCount slots (lowerExpr left le ls).2 provenance →
      GeneratedBuilderState (lowerExpr left le ls).2 →
      NativeRows vt (lowerExpr right le (lowerExpr left le ls).2).2 →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerExpr right le (lowerExpr left le ls).2).2 next ∧
        ((lowerExpr right le (lowerExpr left le ls).2).2.cur.isSome = true → ReplayValue func next
          (lowerExpr right le (lowerExpr left le ls).2).2 (lowerExpr right le (lowerExpr left le ls).2).1 roots (.data (.int integer))) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.bin op left right origin) le ls).2 next ∧
      ((lowerExpr (.bin op left right origin) le ls).2.cur.isSome = true → ReplayValue func next
        (lowerExpr (.bin op left right origin) le ls).2 (lowerExpr (.bin op left right origin) le ls).1 sourceRoots (.data type)) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨leftStart, leftFinish, rightStart, rightFinish, integer, leftTyped, rightTyped, shape⟩ :=
    tyExpr_bin_children source
  subst type
  obtain ⟨leftRoots, sourceMiddle, leftReplay, rest⟩ := (st_bind_ok _ _ _ _).mp replayed
  obtain ⟨rightRoots, sourceAfter, rightReplay, _⟩ := (st_bind_ok _ _ _ _).mp rest
  have exactReplay := rpExpr_bin_after_operands leftReplay rightReplay (op := op) (origin := origin)
  rw [exactReplay] at replayed
  cases replayed
  have rightEffect : EffectRefinement func sourceAfter.eff target := by
    cases aborts : op.mayAbort with
    | false => simpa only [aborts, Bool.false_eq_true, ite_false] using wholeEffect
    | true =>
      have bound : EffectRefinement func { sourceAfter.eff with aborts := true } target := by
        simpa only [aborts, ite_true] using wholeEffect
      exact ⟨bound.reads, bound.writes, bound.grows, bound.shrinks, bound.rebinds,
        fun _ => bound.aborts rfl, bound.outputs, bound.unknown⟩
  have leftEffect := effectRefinement_before_expression rightReplay rightEffect
  let leftRun := lowerExpr left le ls
  let rightRun := lowerExpr right le leftRun.2
  have tailTypes : TypeRun (do
      let ty ← intTyOf leftRun.1
      Goose.Lower.emitDef (.bin op ty leftRun.1 rightRun.1 (some origin))) :=
    TypeRun.bind (types_intTyOf _) fun _ => types_emitDef _
  have rightNative := native.of_prefix (tailTypes le rightRun.2 _ _ rfl)
  have leftNative := rightNative.of_prefix (types_lowerExpr right le leftRun.2 rightRun.1 rightRun.2 rfl)
  obtain ⟨middle, middleReady, leftValue, middleRoots⟩ :=
    leftChild leftStart leftFinish integer leftRoots sourceMiddle leftTyped leftReplay leftEffect generated leftNative
  obtain ⟨last, lastReady, rightValue, lastRoots⟩ :=
    rightChild rightStart rightFinish integer sourceMiddle rightRoots sourceAfter middle rightTyped rightReplay rightEffect
      middleReady (generated.lowerExpr left rfl) rightNative
  have typeRun : intTyOf leftRun.1 le rightRun.2 = ((intTyOf leftRun.1 le rightRun.2).1, rightRun.2) :=
    Prod.ext rfl (by
      simp only [intTyOf, bind_run, valTy_run]
      cases (valTy leftRun.1 le rightRun.2).1 with
      | data type => cases type <;> rfl
      | view => rfl)
  obtain ⟨next, nextReady, nextValue, nextRoots⟩ := lastReady.binary leftReplay rightReplay exactReplay wholeEffect
    (initial := ls) (middle := leftRun.2) rfl rfl typeRun (by
      intro live
      have leftLive := (dead_lowerExpr right).live_before (le := le) rfl live
      exact ⟨Nat.lt_of_lt_of_le (leftValue leftLive).bound (advB_lowerExpr right le leftRun.2 _ _ rfl).vals,
        (rightValue live).bound⟩) originBound
  refine ⟨next, nextReady, ?_, ?_⟩
  · intro live
    have value := nextValue live
    exact ⟨value.bound, value.refined, fun _ => value.scalar rfl⟩
  · intro index bound
    have firstGrowth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, middleReady.roots.valueSize]
      exact (advB_lowerExpr left le ls _ _ rfl).vals
    have secondGrowth : middle.vals.size ≤ last.vals.size := by
      rw [middleReady.roots.valueSize, lastReady.roots.valueSize]
      exact (advB_lowerExpr right le leftRun.2 _ _ rfl).vals
    exact (nextRoots index (Nat.lt_of_lt_of_le bound (Nat.le_trans firstGrowth secondGrowth))).trans
      ((lastRoots index (Nat.lt_of_lt_of_le bound firstGrowth)).trans (middleRoots index bound))

#print axioms typedBinaryNative

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
