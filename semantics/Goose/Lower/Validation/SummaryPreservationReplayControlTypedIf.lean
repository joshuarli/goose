import Goose.Lower.Validation.SummaryPreservationReplayControlIf
import Goose.Lower.Validation.SummaryPreservationSourceEffectCeiling
import Goose.Lower.Validation.SourceStatementTypingControl

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpStmt_if_children {env : PEnv} {condition : Expr} {yes : Core.Block}
    {no : Option Core.Block} {origin : OriginId} {before after : RState}
    (source : rpStmt env (.ifS condition yes no origin) before = .ok ((), after)) :
    ∃ conditionRoots conditionState yesRoots yesRange yesState,
      rpExpr env condition before = .ok (conditionRoots, conditionState) ∧
      rpBlockValue env [] yes conditionState = .ok ((yesRoots, yesRange), yesState) ∧
      match no with
      | none => after = yesState
      | some body => ∃ roots range, rpBlockValue env [] body yesState = .ok ((roots, range), after) := by
  cases no <;> simp only [rpStmt] at source
  all_goals
    obtain ⟨conditionRoots, conditionState, conditionReplay, tail⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨⟨yesRoots, yesRange⟩, yesState, yesReplay, tail⟩ := (st_bind_ok _ _ _ _).mp tail
  case none =>
    exact ⟨conditionRoots, conditionState, yesRoots, yesRange, yesState, conditionReplay, yesReplay,
      congrArg Prod.snd ((st_pure_ok _ _ _).mp tail)⟩
  case some body =>
    obtain ⟨⟨roots, range⟩, state, noReplay, tail⟩ := (st_bind_ok _ _ _ _).mp tail
    have same : after = state := congrArg Prod.snd ((st_pure_ok _ _ _).mp tail)
    subst state
    exact ⟨conditionRoots, conditionState, yesRoots, yesRange, yesState, conditionReplay, yesReplay, roots, range, noReplay⟩

namespace ReplayBuilder

theorem typedIfStatement {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {ls : LS} {upper : Prov}
    {env output : TEnv} {penv : PEnv} {condition : Expr} {yes : Core.Block}
    {no : Option Core.Block} {origin : OriginId} {scope start finish : Nat}
    {before after : RState} (loop : Option LoopCtx)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (source : tyStmt env scope (.ifS condition yes no origin) start = .ok (output, finish))
    (replayed : rpStmt penv (.ifS condition yes no origin) before = .ok ((), after))
    (wholeEffect : EffectRefinement func after.eff target)
    (conditionChild : ∀ tn roots sourceAfter value state,
      tyExpr env condition start = .ok (.bool, tn) →
      rpExpr penv condition before = .ok (roots, sourceAfter) →
      lowerExpr condition le ls = (value, state) →
      EffectRefinement func sourceAfter.eff target →
      ReplayBuilder module results vt func target le scopeCount slots ls upper →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots state next ∧
        (state.cur.isSome = true → value < state.vals.size) ∧
        ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index)
    (yesChild : ∀ tn1 tn2 type roots range sourceBefore sourceAfter conditionValue conditionLS state provenance,
      tyBlock env [] yes tn1 = .ok (type, tn2) →
      rpBlockValue penv [] yes sourceBefore = .ok ((roots, range), sourceAfter) →
      lowerExpr condition le ls = (conditionValue, conditionLS) →
      state = { (fork conditionValue le conditionLS).2 with cur := some conditionLS.blocks.size } →
      EffectRefinement func sourceAfter.eff target →
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerBlock loop [] false yes le state).2 next ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index)
    (noChild : ∀ body, no = some body → ∀ tn1 tn2 type roots range sourceBefore sourceAfter conditionValue conditionLS state provenance,
      tyBlock env [] body tn1 = .ok (type, tn2) →
      rpBlockValue penv [] body sourceBefore = .ok ((roots, range), sourceAfter) →
      lowerExpr condition le ls = (conditionValue, conditionLS) →
      state = { (lowerBlock loop [] false yes le
        { (fork conditionValue le conditionLS).2 with cur := some conditionLS.blocks.size }).2 with cur := some (conditionLS.blocks.size + 1) } →
      EffectRefinement func sourceAfter.eff target →
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerBlock loop [] false body le state).2 next ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerStmt loop (.ifS condition yes no origin) le ls).2 next ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨conditionCounter, yesType, yesCounter, typedCondition, typedYes, typedNo, _⟩ := tyStmt_if_children source
  obtain ⟨conditionRoots, conditionState, yesRoots, yesRange, yesState, replayedCondition, replayedYes, replayedNo⟩ := rpStmt_if_children replayed
  have yesEffect : EffectRefinement func yesState.eff target := by
    cases no with
    | none => simpa only [replayedNo] using wholeEffect
    | some body =>
      obtain ⟨roots, range, checked⟩ := replayedNo
      exact effectRefinement_before_of_replay (rp_mono_all.2.2.2.2.1 penv [] body)
        (rp_rebinds_mono_all.2.2.2.2.1 penv [] body) (rp_flags_mono_all.2.2.2.2.1 penv [] body) checked wholeEffect
  have conditionEffect := effectRefinement_before_of_replay (rp_mono_all.2.2.2.2.1 penv [] yes)
    (rp_rebinds_mono_all.2.2.2.2.1 penv [] yes) (rp_flags_mono_all.2.2.2.2.1 penv [] yes) replayedYes yesEffect
  obtain ⟨middle, conditionReady, conditionBound, conditionPrefix⟩ :=
    conditionChild conditionCounter conditionRoots conditionState _ _ typedCondition replayedCondition rfl conditionEffect ready
  obtain ⟨next, generated, retained⟩ := conditionReady.ifStatement (no := no) (origin := origin) loop rfl conditionBound
    (fun state provenance checkpoint stateReady => yesChild conditionCounter yesCounter yesType yesRoots yesRange
      conditionState yesState _ _ state provenance typedYes replayedYes rfl checkpoint yesEffect stateReady)
    (by
      intro body selected state provenance checkpoint stateReady
      subst no
      obtain ⟨type, typed⟩ := typedNo
      obtain ⟨roots, range, checked⟩ := replayedNo
      exact noChild body rfl yesCounter finish type roots range yesState after _ _ state provenance
        typed checked rfl checkpoint wholeEffect stateReady)
  refine ⟨next, generated, ?_⟩
  intro index bound
  have growth : upper.vals.size ≤ middle.vals.size := by
    rw [ready.roots.valueSize, conditionReady.roots.valueSize]
    exact (advB_lowerExpr condition le ls _ _ rfl).vals
  exact (retained index (Nat.lt_of_lt_of_le bound growth)).trans (conditionPrefix index bound)

end ReplayBuilder
end Goose.Lower.Validation.SummaryPreservation
