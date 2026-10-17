import Goose.Lower.Validation.SummaryPreservationReplayArgumentSource
import Goose.Lower.Validation.SummaryPreservationSourceEffectCeiling

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem typedArgument {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {ls : LS} {upper : Prov}
    {env : TEnv} {penv : PEnv} {start finish : Nat} {before after : RState}
    {sourceRoots : List RootRef} (argument : Arg)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (typed : ArgumentTyping env argument start finish)
    (replayed : ArgumentReplay penv argument before sourceRoots after)
    (expressionChild : ∀ expression type, argument = .byVal expression →
      tyExpr env expression start = .ok (type, finish) →
      rpExpr penv expression before = .ok (sourceRoots, after) →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerExpr expression le ls).2 next ∧
        ((lowerExpr expression le ls).2.cur.isSome = true →
          ReplayValue func next (lowerExpr expression le ls).2
            (lowerExpr expression le ls).1 sourceRoots (.data type)) ∧
        ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index)
    (placeChild : ∀ mutability place info, argument = .byRef mutability place →
      tyPlace env place start = .ok (info, finish) →
      rpPlace penv place before = .ok (sourceRoots, after) →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerPlace place le ls).2 next ∧
        ((lowerPlace place le ls).2.cur.isSome = true →
          (lowerPlace place le ls).1 < (lowerPlace place le ls).2.vals.size ∧
          RootsRefine func (rootsAt next.vals (lowerPlace place le ls).1) sourceRoots) ∧
        ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerArg argument le ls).2 next ∧
      ((lowerArg argument le ls).2.cur.isSome = true →
        (lowerArg argument le ls).1 < (lowerArg argument le ls).2.vals.size ∧
        RootsRefine func (rootsAt next.vals (lowerArg argument le ls).1) sourceRoots) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  apply ready.argument argument replayed
  · intro expression same source
    subst argument
    obtain ⟨type, typedExpression⟩ := typed
    obtain ⟨next, generated, returned, retained⟩ := expressionChild expression type rfl typedExpression source
    exact ⟨next, generated, fun live => ⟨(returned live).bound, (returned live).refined⟩, retained⟩
  · intro mutability place same source
    subst argument
    obtain ⟨info, typedPlace⟩ := typed
    exact placeChild mutability place info rfl typedPlace source

theorem typedArguments {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {ls : LS} {upper : Prov}
    {typingEnv : TEnv} {env : PEnv} {callee : Impl} {start finish : Nat}
    (syntaxArgs : List Arg) (parameters : List Param)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (typed : tyArgs typingEnv callee parameters syntaxArgs start = .ok ((), finish))
    (shape : parameters.length = syntaxArgs.length)
    (step : ∀ argument, argument ∈ syntaxArgs → ∀ tn1 tn2 before after roots state provenance,
      ArgumentTyping typingEnv argument tn1 tn2 → ArgumentReplay env argument before roots after →
      EffectRefinement func after.eff target →
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerArg argument le state).2 next ∧
        ((lowerArg argument le state).2.cur.isSome = true →
          (lowerArg argument le state).1 < (lowerArg argument le state).2.vals.size ∧
          RootsRefine func (rootsAt next.vals (lowerArg argument le state).1) roots) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index)
    {before after : RState} {sourceRoots : List (List RootRef)}
    (source : rpArgs env syntaxArgs before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerArgs syntaxArgs le ls).2 next ∧
      ((lowerArgs syntaxArgs le ls).2.cur.isSome = true →
        (lowerArgs syntaxArgs le ls).1.length = syntaxArgs.length ∧
        ∀ (index : Nat) (value : ValueId), (lowerArgs syntaxArgs le ls).1[index]? = some value →
          value < (lowerArgs syntaxArgs le ls).2.vals.size ∧
          ∃ roots, sourceRoots[index]? = some roots ∧ RootsRefine func (rootsAt next.vals value) roots) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  induction syntaxArgs generalizing before after sourceRoots ls upper start parameters with
  | nil =>
    refine ⟨upper, ready, ?_, fun _ _ => rfl⟩
    simp [lowerArgs, pure_run]
  | cons argument rest ih =>
    cases parameters with
    | nil => simp at shape
    | cons parameter parameters =>
      obtain ⟨middleCounter, headTyped, tailTyped⟩ := tyArgs_cons_children typed
      obtain ⟨roots, remaining, middleSource, firstReplay, restReplay, rfl⟩ := rpArgs_cons_contract source
      have firstEffect := effectRefinement_before_of_replay
        (rp_mono_all.2.2.2.2.2.2.2.2.1 env rest)
        (rp_rebinds_mono_all.2.2.2.2.2.2.2.2.1 env rest)
        (rp_flags_mono_all.2.2.2.2.2.2.2.2.1 env rest) restReplay wholeEffect
      obtain ⟨middle, middleReady, firstValue, middleRoots⟩ :=
        step argument (by simp) start middleCounter before middleSource roots ls upper
          headTyped firstReplay firstEffect ready
      obtain ⟨next, nextReady, tailValues, nextRoots⟩ := ih parameters middleReady tailTyped
        (by simpa using shape) (fun child member => step child (by simp [member])) restReplay wholeEffect
      let first := lowerArg argument le ls
      let tail := lowerArgs rest le first.2
      have whole : lowerArgs (argument :: rest) le ls = (first.1 :: tail.1, tail.2) := by
        simp only [lowerArgs, bind_run, pure_run]
        rfl
      have valGrowth := (advB_lowerArgs rest le first.2 tail.1 tail.2 rfl).vals
      rw [whole]
      refine ⟨next, nextReady, ?_, ?_⟩
      · intro live
        have firstLive : first.2.cur.isSome = true :=
          (dead_lowerArgs rest).live_before (le := le) (before := first.2)
            (after := tail.2) (result := tail.1) rfl live
        obtain ⟨tailLength, tailValue⟩ := tailValues live
        refine ⟨by simpa using congrArg Nat.succ tailLength, ?_⟩
        intro index value row
        cases index with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at row
          subst value
          obtain ⟨bound, refined⟩ := firstValue firstLive
          refine ⟨Nat.lt_of_lt_of_le bound valGrowth, roots, rfl, ?_⟩
          rw [nextRoots first.1 (by rw [middleReady.roots.valueSize]; exact bound)]
          exact refined
        | succ index =>
          simp only [List.getElem?_cons_succ] at row
          obtain ⟨bound, sourceRoots, sourceRow, refined⟩ := tailValue index value row
          exact ⟨bound, sourceRoots, sourceRow, refined⟩
      · intro index bound
        have growth : upper.vals.size ≤ middle.vals.size := by
          rw [ready.roots.valueSize, middleReady.roots.valueSize]
          exact (advB_lowerArg argument le ls first.1 first.2 rfl).vals
        exact (nextRoots index (Nat.lt_of_lt_of_le bound growth)).trans (middleRoots index bound)

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
