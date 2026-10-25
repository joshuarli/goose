import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsPhysicalContracts

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty}
  {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat}
  {siteRoot anchor : DemandNode} {siteTargets : List BlockId}

theorem typedPhysicalArgumentsOccurrence (arguments : List Arg)
    (step : ∀ argument ∈ arguments, ∀ state provenance,
      PhysicalArgumentOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
        anchor argument state provenance) :
    ∀ initial upper, PhysicalArgumentsOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount
      siteRoot siteTargets anchor arguments initial upper := by
  intro initial upper anchored paths callee parameters start finish before after sourceRoots
    typed shape source wholeEffect ready sites targets generated native metadata continuation
  let le := lowerEnv env.mod env.impl.vars returnTypes
  cases arguments with
  | nil =>
    refine ⟨upper, ready, ?_, fun _ _ => rfl, ?_, sites, ?_⟩
    · simp only [lowerArgs, pure_run, List.length_nil, List.getElem?_nil, reduceCtorEq,
        false_implies, implies_true, and_self]
    · exact EmitsOnly.refl _ _
    · intro live index value syntaxArg row sourceRow
      simp [lowerArgs, pure_run] at row
  | cons argument rest =>
    cases parameters with
    | nil => simp at shape
    | cons parameter parameters =>
      obtain ⟨middleCounter, headTyped, tailTyped⟩ := tyArgs_cons_children typed
      obtain ⟨roots, middleSource, remaining, firstReplay, restReplay, rfl⟩ := rpArgs_cons_contract source
      have firstEffect := effectRefinement_before_of_replay
        (rp_mono_all.2.2.2.2.2.2.2.2.1 env rest)
        (rp_rebinds_mono_all.2.2.2.2.2.2.2.2.1 env rest)
        (rp_flags_mono_all.2.2.2.2.2.2.2.2.1 env rest) restReplay wholeEffect
      obtain ⟨middle, middleReady, firstValue, middleRoots, firstLedger, middleSites, firstPhysical⟩ :=
        step argument (by simp) initial upper anchored (paths argument (by simp))
          start middleCounter before middleSource roots headTyped firstReplay firstEffect ready sites targets generated
          (native.of_prefix (types_lowerArgs rest le (lowerArg argument le initial).2 _ _ rfl))
          (metadata.of_advance (advB_lowerArgs rest le (lowerArg argument le initial).2 _ _ rfl))
          (continuation.of_advance (advB_lowerArgs rest le (lowerArg argument le initial).2 _ _ rfl))
      obtain ⟨next, nextReady, tailValues, nextRoots, tailLedger, nextSites, tailPhysical⟩ :=
        typedPhysicalArgumentsOccurrence rest (fun child member => step child (by simp [member]))
          (lowerArg argument le initial).2 middle anchored
          (fun child member => paths child (by simp [member])) callee parameters middleCounter finish
          middleSource after remaining tailTyped (by simpa using shape) restReplay wholeEffect
          middleReady middleSites (targets.mono firstLedger.extension)
          (generated.lowerArg argument rfl) native metadata continuation
      let first := lowerArg argument le initial
      let tail := lowerArgs rest le first.2
      have whole : lowerArgs (argument :: rest) le initial = (first.1 :: tail.1, tail.2) := by
        simp only [lowerArgs, bind_run, pure_run]
        rfl
      have valGrowth := (advB_lowerArgs rest le first.2 tail.1 tail.2 rfl).vals
      have ghostGrowth : middle.vals.size ≤ next.vals.size := by
        rw [middleReady.roots.valueSize, nextReady.roots.valueSize]
        exact valGrowth
      have firstFinalLedger := firstLedger.retained ghostGrowth nextRoots
      dsimp only [le] at whole
      rw [whole]
      refine ⟨next, nextReady, ?_, ?_, firstFinalLedger.trans tailLedger, nextSites, ?_⟩
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
          obtain ⟨bound, refined, occurrence⟩ := firstValue firstLive
          refine ⟨Nat.lt_of_lt_of_le bound valGrowth, ⟨roots, rfl, ?_⟩,
            occurrence.retained ghostGrowth nextRoots⟩
          rw [nextRoots first.1 (by rw [middleReady.roots.valueSize]; exact bound)]
          exact refined
        | succ index =>
          simp only [List.getElem?_cons_succ] at row
          obtain ⟨bound, ⟨childRoots, sourceRow, refined⟩, occurrence⟩ := tailValue index value row
          exact ⟨bound, ⟨childRoots, sourceRow, refined⟩, occurrence⟩
      · intro index bound
        have growth : upper.vals.size ≤ middle.vals.size := by
          rw [ready.roots.valueSize, middleReady.roots.valueSize]
          exact (advB_lowerArg argument le initial first.1 first.2 rfl).vals
        exact (nextRoots index (Nat.lt_of_lt_of_le bound growth)).trans (middleRoots index bound)
      · intro live index value syntaxArg row sourceRow
        cases index with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at row sourceRow
          subst value syntaxArg
          have firstLive : first.2.cur.isSome = true :=
            (dead_lowerArgs rest).live_before (le := le) (before := first.2)
              (after := tail.2) (result := tail.1) rfl live
          exact (firstPhysical firstLive).retained
            (by rw [middleReady.roots.valueSize]; exact (firstValue firstLive).1) nextRoots
        | succ index =>
          simp only [List.getElem?_cons_succ] at row sourceRow
          exact tailPhysical live index value syntaxArg row sourceRow
termination_by arguments.length

#print axioms typedPhysicalArgumentsOccurrence

end Goose.Lower.Validation.ReplacementContentFlowSource
