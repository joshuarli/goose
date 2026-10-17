import Goose.Lower.Validation.SummaryPreservationReplayTypedArguments
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem typedGlobalArgumentsNative {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {ls : LS} {upper : Prov}
    {typingEnv : TEnv} {env : PEnv} {callee : Impl} {start finish : Nat}
    (syntaxArgs : List Arg) (parameters : List Param)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (typed : tyArgs typingEnv callee parameters syntaxArgs start = .ok ((), finish))
    (shape : parameters.length = syntaxArgs.length)
    (step : ∀ earlier argument suffix, syntaxArgs = earlier ++ argument :: suffix →
      ∀ tn1 tn2 before after roots provenance,
      let state := (lowerArgs earlier le ls).2
      ArgumentTyping typingEnv argument tn1 tn2 → ArgumentReplay env argument before roots after →
      EffectRefinement func after.eff target →
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      GeneratedBuilderState state →
      NativeRows vt (lowerArg argument le state).2 →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerArg argument le state).2 next ∧
        ((lowerArg argument le state).2.cur.isSome = true →
          (lowerArg argument le state).1 < (lowerArg argument le state).2.vals.size ∧
          RootsRefine func (rootsAt next.vals (lowerArg argument le state).1) roots) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index)
    {before after : RState} {sourceRoots : List (List RootRef)}
    (source : rpArgs env syntaxArgs before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerArgs syntaxArgs le ls).2) :
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
      obtain ⟨roots, middleSource, remaining, firstReplay, restReplay, rfl⟩ := rpArgs_cons_contract source
      have firstEffect := effectRefinement_before_of_replay
        (rp_mono_all.2.2.2.2.2.2.2.2.1 env rest)
        (rp_rebinds_mono_all.2.2.2.2.2.2.2.2.1 env rest)
        (rp_flags_mono_all.2.2.2.2.2.2.2.2.1 env rest) restReplay wholeEffect
      obtain ⟨middle, middleReady, firstValue, middleRoots⟩ :=
        step [] argument rest rfl start middleCounter before middleSource roots upper
          headTyped firstReplay firstEffect ready generated
          (native.of_prefix (types_lowerArgs rest le (lowerArg argument le ls).2 _ _ rfl))
      have tailStep : ∀ earlier child suffix, rest = earlier ++ child :: suffix →
          ∀ tn1 tn2 sourceBefore sourceAfter childRoots provenance,
          let state := (lowerArgs earlier le (lowerArg argument le ls).2).2
          ArgumentTyping typingEnv child tn1 tn2 → ArgumentReplay env child sourceBefore childRoots sourceAfter →
          EffectRefinement func sourceAfter.eff target →
          ReplayBuilder module results vt func target le scopeCount slots state provenance →
          GeneratedBuilderState state → NativeRows vt (lowerArg child le state).2 →
          ∃ next, ReplayBuilder module results vt func target le scopeCount slots (lowerArg child le state).2 next ∧
            ((lowerArg child le state).2.cur.isSome = true →
              (lowerArg child le state).1 < (lowerArg child le state).2.vals.size ∧
              RootsRefine func (rootsAt next.vals (lowerArg child le state).1) childRoots) ∧
            ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index := by
        intro earlier child suffix selected
        have whole : argument :: rest = (argument :: earlier) ++ child :: suffix := by
          simpa only [List.cons_append] using congrArg (List.cons argument) selected
        simpa only [lowerArgs, bind_run, pure_run] using step (argument :: earlier) child suffix whole
      obtain ⟨next, nextReady, tailValues, nextRoots⟩ := ih parameters middleReady tailTyped
        (by simpa using shape) tailStep restReplay wholeEffect
          (generated.lowerArg argument rfl) native
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
        refine ⟨by simpa only [lowerArgs, pure_run, List.length_cons] using congrArg Nat.succ tailLength, ?_⟩
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

#print axioms typedGlobalArgumentsNative

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
