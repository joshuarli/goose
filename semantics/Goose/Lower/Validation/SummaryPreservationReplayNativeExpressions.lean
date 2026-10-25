import Goose.Lower.Validation.SummaryPreservationReplayTypedPlacesContracts
import Goose.Lower.Validation.ExpressionTypingAggregateOps

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem typedExpressionsNative {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {ls : LS} {upper : Prov}
    {typingEnv : TEnv} {env : PEnv} {start finish : Nat}
    (expressions : List Expr) (types : List Ty)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (typed : tyStructExprs typingEnv types expressions start = .ok ((), finish))
    (step : ∀ earlier expression suffix, expressions = earlier ++ expression :: suffix →
      ∀ type tn1 tn2 before after roots provenance,
      let entry := (lowerExprs earlier le ls).2
      tyExpr typingEnv expression tn1 = .ok (type, tn2) →
      rpExpr env expression before = .ok (roots, after) →
      EffectRefinement func after.eff target →
      ReplayBuilder module results vt func target le scopeCount slots entry provenance →
      GeneratedBuilderState entry → NativeRows vt (lowerExpr expression le entry).2 →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerExpr expression le entry).2 next ∧
        ((lowerExpr expression le entry).2.cur.isSome = true →
          ReplayValue func next (lowerExpr expression le entry).2
            (lowerExpr expression le entry).1 roots (.data type)) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index)
    {before after : RState}
    (source : rpExprs env expressions before = .ok ((), after))
    (wholeEffect : EffectRefinement func after.eff target)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerExprs expressions le ls).2) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExprs expressions le ls).2 next ∧
      ((lowerExprs expressions le ls).2.cur.isSome = true →
        ∀ value ∈ (lowerExprs expressions le ls).1, value < (lowerExprs expressions le ls).2.vals.size) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  induction expressions generalizing before after ls upper start types with
  | nil =>
    refine ⟨upper, ready, ?_, fun _ _ => rfl⟩
    simp [lowerExprs, pure_run]
  | cons expression rest ih =>
    cases types with
    | nil => exact ((rej_ok _ _ _ _).mp typed).elim
    | cons fieldType fieldTypes =>
      simp only [tyStructExprs] at typed
      obtain ⟨headType, middleCounter, headTyped, tailTyped⟩ := (st_bind_ok _ _ _ _).mp typed
      by_cases same : (headType == fieldType) = true
      · simp only [same, ite_true] at tailTyped
        obtain ⟨roots, middleSource, firstReplay, restReplay⟩ :=
          (st_bind_ok _ _ _ _).mp source
        have firstEffect := effectRefinement_before_of_replay
          (rp_mono_all.2.2.2.1 env rest) (rp_rebinds_mono_all.2.2.2.1 env rest)
          (rp_flags_mono_all.2.2.2.1 env rest) restReplay wholeEffect
        have headNative := native.of_prefix
          (types_lowerExprs rest le (lowerExpr expression le ls).2 _ _ rfl)
        obtain ⟨middle, middleReady, firstValue, middleRoots⟩ :=
          step [] expression rest rfl headType start middleCounter before middleSource roots upper
            headTyped firstReplay firstEffect ready generated headNative
        have tailStep : ∀ earlier child suffix, rest = earlier ++ child :: suffix →
            ∀ type tn1 tn2 sourceBefore sourceAfter childRoots provenance,
            let entry := (lowerExprs earlier le (lowerExpr expression le ls).2).2
            tyExpr typingEnv child tn1 = .ok (type, tn2) →
            rpExpr env child sourceBefore = .ok (childRoots, sourceAfter) →
            EffectRefinement func sourceAfter.eff target →
            ReplayBuilder module results vt func target le scopeCount slots entry provenance →
            GeneratedBuilderState entry → NativeRows vt (lowerExpr child le entry).2 →
            ∃ next, ReplayBuilder module results vt func target le scopeCount slots
                (lowerExpr child le entry).2 next ∧
              ((lowerExpr child le entry).2.cur.isSome = true →
                ReplayValue func next (lowerExpr child le entry).2
                  (lowerExpr child le entry).1 childRoots (.data type)) ∧
              ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index := by
          intro earlier child suffix shape
          have whole : expression :: rest = (expression :: earlier) ++ child :: suffix := by
            simpa only [List.cons_append] using congrArg (List.cons expression) shape
          simpa only [lowerExprs, bind_run, pure_run] using step (expression :: earlier) child suffix whole
        obtain ⟨next, nextReady, tailValues, nextRoots⟩ :=
          ih fieldTypes middleReady tailTyped tailStep restReplay wholeEffect
            (generated.lowerExpr expression rfl) native
        let first := lowerExpr expression le ls
        let tail := lowerExprs rest le first.2
        have whole : lowerExprs (expression :: rest) le ls = (first.1 :: tail.1, tail.2) := by
          simp only [lowerExprs, bind_run, pure_run]
          rfl
        have valGrowth := (advB_lowerExprs rest le first.2 tail.1 tail.2 rfl).vals
        rw [whole]
        refine ⟨next, nextReady, ?_, ?_⟩
        · intro live value member
          rcases List.mem_cons.mp member with head | tailMember
          · subst value
            have firstLive : first.2.cur.isSome = true :=
              (dead_lowerExprs rest).live_before (le := le) (before := first.2)
                (after := tail.2) (result := tail.1) rfl live
            exact Nat.lt_of_lt_of_le (firstValue firstLive).bound valGrowth
          · exact tailValues live value tailMember
        · intro index bound
          have growth : upper.vals.size ≤ middle.vals.size := by
            rw [ready.roots.valueSize, middleReady.roots.valueSize]
            exact (advB_lowerExpr expression le ls first.1 first.2 rfl).vals
          exact (nextRoots index (Nat.lt_of_lt_of_le bound growth)).trans (middleRoots index bound)
      · simp [same, chk] at tailTyped

theorem typedExpressionsAsNative {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {ls : LS} {upper : Prov}
    {typingEnv : TEnv} {env : PEnv} {start finish : Nat}
    (expressions : List Expr) (element : Ty)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (typed : tyExprsAs typingEnv element expressions start = .ok ((), finish))
    (step : ∀ earlier expression suffix, expressions = earlier ++ expression :: suffix →
      ∀ type tn1 tn2 before after roots provenance,
      let entry := (lowerExprs earlier le ls).2
      tyExpr typingEnv expression tn1 = .ok (type, tn2) →
      rpExpr env expression before = .ok (roots, after) →
      EffectRefinement func after.eff target →
      ReplayBuilder module results vt func target le scopeCount slots entry provenance →
      GeneratedBuilderState entry → NativeRows vt (lowerExpr expression le entry).2 →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerExpr expression le entry).2 next ∧
        ((lowerExpr expression le entry).2.cur.isSome = true →
          ReplayValue func next (lowerExpr expression le entry).2
            (lowerExpr expression le entry).1 roots (.data type)) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index)
    {before after : RState}
    (source : rpExprs env expressions before = .ok ((), after))
    (wholeEffect : EffectRefinement func after.eff target)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerExprs expressions le ls).2) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExprs expressions le ls).2 next ∧
      ((lowerExprs expressions le ls).2.cur.isSome = true →
        ∀ value ∈ (lowerExprs expressions le ls).1, value < (lowerExprs expressions le ls).2.vals.size) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  exact typedExpressionsNative expressions (List.replicate expressions.length element) ready
    (tyExprsAs_structExprs typed) step source wholeEffect generated native

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
