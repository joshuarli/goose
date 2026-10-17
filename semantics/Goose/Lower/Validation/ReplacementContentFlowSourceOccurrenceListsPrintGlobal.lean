import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceListsPrintGlobalContracts
import Goose.Lower.Validation.SummaryPreservationStoppedGraph

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

private theorem occurrence_print_stopped (arguments : List PrintArg) : StoppedGraph (lowerPrintArgs arguments) := by
  induction arguments with
  | nil => exact StoppedGraph.pure _
  | cons argument rest ih =>
    cases argument with
    | text _ => exact StoppedGraph.bind ih fun _ => StoppedGraph.pure _
    | expr expression => exact StoppedGraph.bind (stopped_lowerExpr expression) fun _ =>
        StoppedGraph.bind ih fun _ => StoppedGraph.pure _

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty}
  {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat}
  {siteRoot anchor : DemandNode} {siteTargets : List BlockId}

theorem typedGlobalPrintArgumentsOccurrence (arguments : List PrintArg)
    (step : ∀ expression, .expr expression ∈ arguments → ∀ state provenance,
      GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
        expression state provenance) :
    ∀ initial upper, GlobalPrintArgumentsOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount
      siteRoot siteTargets anchor arguments initial upper := by
  intro initial upper anchored paths start finish before after typed source wholeEffect
    ready sites targets generated native metadata continuation
  let le := lowerEnv env.mod env.impl.vars returnTypes
  cases arguments with
  | nil =>
    refine ⟨upper, ready, ?_, fun _ _ => rfl, ?_, sites⟩
    · simp [lowerPrintArgs, pure_run]
    · exact EmitsOnly.refl _ _
  | cons argument rest =>
    cases argument with
    | text text =>
      obtain ⟨next, completed, values, retained, ledger, nextSites⟩ :=
        typedGlobalPrintArgumentsOccurrence rest (fun expression member => step expression (by simp [member]))
          initial upper anchored (fun expression member => paths expression (by simp [member]))
          start finish before after typed source wholeEffect ready sites targets generated native metadata continuation
      refine ⟨next, completed, ?_, retained, ledger, nextSites⟩
      simpa only [lowerPrintArgs, bind_run, pure_run, List.flatMap_cons, PrintPart.uses, List.nil_append] using values
    | expr expression =>
      obtain ⟨type, middleCounter, expressionTyped, tailTyped⟩ := (st_bind_ok _ _ _ _).mp typed
      have tailTyped : tyPrintArgs typingEnv rest middleCounter = .ok ((), finish) := by
        cases type <;> first | exact tailTyped | exact ((rej_ok _ _ _ _).mp tailTyped).elim
      obtain ⟨roots, middleState, expressionReplay, tailReplay⟩ := (st_bind_ok _ _ _ _).mp source
      have expressionEffect := effectRefinement_before_of_replay
        (rp_mono_all.2.2.2.2.2.2.2.1 env rest) (rp_rebinds_mono_all.2.2.2.2.2.2.2.1 env rest)
        (rp_flags_mono_all.2.2.2.2.2.2.2.1 env rest) tailReplay wholeEffect
      obtain ⟨childPath, childSource⟩ := paths expression (by simp)
      have childAtSite : ∃ path, DemandNodeAt siteRoot path (.expression expression) := by
        obtain ⟨outerPath, outer⟩ := anchored
        exact ⟨outerPath ++ childPath, sourcePath_append outer childSource⟩
      let lowered := lowerExpr expression le initial
      have expressionNative := native.of_prefix (types_lowerPrintArgs rest le lowered.2 _ _ rfl)
      obtain ⟨middle, expressionReady, expressionValue, expressionPrefix, expressionLedger, middleSites⟩ :=
        step expression (by simp) initial upper childAtSite type start middleCounter before middleState roots
          expressionTyped expressionReplay expressionEffect ready sites targets generated expressionNative
          (metadata.of_advance (advB_lowerPrintArgs rest le lowered.2 _ _ rfl))
          (continuation.of_advance (advB_lowerPrintArgs rest le lowered.2 _ _ rfl))
      obtain ⟨next, completed, values, retained, tailLedger, nextSites⟩ :=
        typedGlobalPrintArgumentsOccurrence rest (fun value member => step value (by simp [member]))
          lowered.2 middle anchored (fun value member => paths value (by simp [member]))
          middleCounter finish middleState after tailTyped tailReplay wholeEffect expressionReady middleSites
          (targets.mono expressionLedger.extension) (generated.lowerExpr expression rfl) native metadata continuation
      have valGrowth := (advB_lowerPrintArgs rest le lowered.2 _ _ rfl).vals
      have ghostGrowth : middle.vals.size ≤ next.vals.size := by
        rw [expressionReady.roots.valueSize, completed.roots.valueSize]
        exact valGrowth
      have firstFinalLedger := (expressionLedger.underRoot childSource).retained ghostGrowth retained
      refine ⟨next, completed, ?_, ?_, firstFinalLedger.trans tailLedger, nextSites⟩
      · intro live value member
        simp only [lowerPrintArgs, bind_run, pure_run, List.flatMap_cons, PrintPart.uses, List.singleton_append,
          List.mem_cons] at member
        rcases member with rfl | tailMember
        · have childLive : lowered.2.cur.isSome = true := by
            cases current : lowered.2.cur with
            | some block => rfl
            | none =>
              have dead := (occurrence_print_stopped rest le lowered.2 _ _ rfl current).1
              change (lowerPrintArgs rest le lowered.2).2.cur.isSome = true at live
              rw [dead] at live
              cases live
          have returned := expressionValue childLive
          have occurrence : OperandOccurrence env anchor func middle lowered.1 := by
            refine ⟨childPath, .expression expression, before, roots, middleState,
              childSource, SourceNodeRoots.expression rfl expressionReplay, ?_, returned.refined⟩
            rw [expressionReady.roots.valueSize]
            exact returned.bound
          exact ⟨Nat.lt_of_lt_of_le returned.bound valGrowth, occurrence.retained ghostGrowth retained⟩
        · exact values live value tailMember
      · intro old bound
        have grows : upper.vals.size ≤ middle.vals.size := by
          rw [ready.roots.valueSize, expressionReady.roots.valueSize]
          exact (advB_lowerExpr expression le initial _ _ rfl).vals
        exact (retained old (Nat.lt_of_lt_of_le bound grows)).trans (expressionPrefix old bound)
termination_by arguments.length

end Goose.Lower.Validation.ReplacementContentFlowSource
