import Goose.Lower.Validation.SummaryPreservationReplayIf
import Goose.Lower.Validation.SummaryPreservationSourceEffectCeiling

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem typedIfExpression {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {ls : LS} {upper : Prov}
    {env : TEnv} {penv : PEnv} {condition : Expr} {yes no : Core.Block}
    {start finish : Nat} {type : Ty} {before after : RState} {sourceRoots : List RootRef}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (source : tyExpr env (.ifE condition yes no) start = .ok (type, finish))
    (replayed : rpExpr penv (.ifE condition yes no) before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (conditionChild : ∀ tn2 roots sourceAfter state provenance,
      tyExpr env condition start = .ok (.bool, tn2) →
      rpExpr penv condition before = .ok (roots, sourceAfter) →
      EffectRefinement func sourceAfter.eff target →
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerExpr condition le state).2 next ∧
        ((lowerExpr condition le state).2.cur.isSome = true →
          ReplayValue func next (lowerExpr condition le state).2
            (lowerExpr condition le state).1 roots (.data .bool)) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index)
    (blockChild : ∀ body, body = yes ∨ body = no → ∀ tn1 tn2 roots range sourceBefore sourceAfter state provenance,
      tyBlock (exprEnv env) [] body tn1 = .ok (type, tn2) →
      rpBlockValue penv [] body sourceBefore = .ok ((roots, range), sourceAfter) →
      EffectRefinement func sourceAfter.eff target →
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerBlock none [] true body le state).2 next ∧
        ((lowerBlock none [] true body le state).2.cur.isSome = true →
          ReplayValue func next (lowerBlock none [] true body le state).2
            (lowerBlock none [] true body le state).1 roots (.data type)) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.ifE condition yes no) le ls).2 next ∧
      ((lowerExpr (.ifE condition yes no) le ls).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.ifE condition yes no) le ls).2
          (lowerExpr (.ifE condition yes no) le ls).1 sourceRoots (.data type)) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨conditionCounter, yesCounter, typedCondition, typedYes, typedNo⟩ := tyExpr_ifE_children source
  obtain ⟨conditionRoots, conditionState, yesRoots, yesRange, yesState, noRoots, noRange,
    replayedCondition, replayedYes, replayedNo, _rootUnion⟩ := rpExpr_ifE_children replayed
  have yesEffect := effectRefinement_before_of_replay
    (rp_mono_all.2.2.2.2.1 penv [] no)
    (rp_rebinds_mono_all.2.2.2.2.1 penv [] no)
    (rp_flags_mono_all.2.2.2.2.1 penv [] no) replayedNo wholeEffect
  have conditionEffect := effectRefinement_before_of_replay
    (rp_mono_all.2.2.2.2.1 penv [] yes)
    (rp_rebinds_mono_all.2.2.2.2.1 penv [] yes)
    (rp_flags_mono_all.2.2.2.2.1 penv [] yes) replayedYes yesEffect
  obtain ⟨middle, conditionReady, conditionValue, conditionPrefix⟩ :=
    conditionChild conditionCounter conditionRoots conditionState ls upper typedCondition
      replayedCondition conditionEffect ready
  let generatedCondition := lowerExpr condition le ls
  obtain ⟨next, completed, returned, retained⟩ := conditionReady.ifExpression (.data type) rfl
    (fun live => (conditionValue live).bound) replayedCondition replayedYes replayedNo replayed
    (fun state provenance _live _entry stateReady => blockChild yes (Or.inl rfl) conditionCounter yesCounter
      yesRoots yesRange conditionState yesState state provenance typedYes replayedYes yesEffect stateReady)
    (fun state provenance _live _entry stateReady => blockChild no (Or.inr rfl) yesCounter finish
      noRoots noRange yesState after state provenance typedNo replayedNo wholeEffect stateReady)
  refine ⟨next, completed, returned, ?_⟩
  intro index bound
  have growth : upper.vals.size ≤ middle.vals.size := by
    rw [ready.roots.valueSize, conditionReady.roots.valueSize]
    exact (advB_lowerExpr condition le ls generatedCondition.1 generatedCondition.2 rfl).vals
  exact (retained index (Nat.lt_of_lt_of_le bound growth)).trans (conditionPrefix index bound)

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
