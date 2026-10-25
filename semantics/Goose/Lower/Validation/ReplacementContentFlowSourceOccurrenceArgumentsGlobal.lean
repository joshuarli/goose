import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsGlobalContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessBorrow

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty}
  {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat}
  {siteRoot anchor : DemandNode} {siteTargets : List BlockId}

theorem typedGlobalArgumentOccurrence (argument : Arg)
    (expressionChild : ∀ expression, argument = .byVal expression → ∀ state provenance,
      GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
        expression state provenance)
    (placeChild : ∀ mutability place, argument = .byRef mutability place → ∀ state provenance,
      GlobalPlaceOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
        place state provenance) :
    ∀ initial upper, GlobalArgumentOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount
      siteRoot siteTargets anchor argument initial upper := by
  intro initial upper anchored path start finish before after sourceRoots typed replay wholeEffect
    ready sites targets generated native metadata continuation
  let le := lowerEnv env.mod env.impl.vars returnTypes
  obtain ⟨outerPath, outer⟩ := anchored
  obtain ⟨childPath, childSource⟩ := path
  cases argument with
  | byVal expression =>
    obtain ⟨type, typed⟩ := typed
    have childAtSite : ∃ path, DemandNodeAt siteRoot path (.expression expression) :=
      ⟨outerPath ++ childPath, sourcePath_append outer childSource⟩
    obtain ⟨next, completed, returned, retained, ledger, nextSites⟩ :=
      expressionChild expression rfl initial upper childAtSite type start finish before after sourceRoots
        typed replay wholeEffect ready sites targets generated native metadata continuation
    refine ⟨next, completed, ?_, retained, ledger.underRoot childSource, nextSites⟩
    intro live
    have value := returned live
    refine ⟨value.bound, value.refined, childPath, .expression expression, before, sourceRoots, after,
      childSource, SourceNodeRoots.expression rfl replay, ?_, value.refined⟩
    rw [completed.roots.valueSize]
    exact value.bound
  | byRef mutability place =>
    obtain ⟨info, typed⟩ := typed
    have childAtSite : ∃ path, DemandNodeAt siteRoot path (.place place) :=
      ⟨outerPath ++ childPath, sourcePath_append outer childSource⟩
    have placeNative := native.of_prefix
      (types_borrowTo mutability (lowerPlace place le initial).1 le (lowerPlace place le initial).2 _ _ rfl)
    obtain ⟨middle, middleReady, address, middleRoots, placeLedger, middleSites⟩ :=
      placeChild mutability place rfl initial upper childAtSite info start finish before after sourceRoots
        typed replay wholeEffect ready sites targets generated placeNative
        (metadata.of_advance (advB_borrowTo mutability (lowerPlace place le initial).1 le
          (lowerPlace place le initial).2 _ _ rfl))
        (continuation.of_advance (advB_borrowTo mutability (lowerPlace place le initial).1 le
          (lowerPlace place le initial).2 _ _ rfl))
    obtain ⟨next, nextReady, returned, nextRoots, borrowedLedger, nextSites⟩ :=
      borrowReferenceOccurrence (root := anchor) mutability Ty.unit (lowerPlace place le initial).1
        sourceRoots middleReady middleSites address
    let first := lowerPlace place le initial
    let borrowed := borrowTo mutability first.1 le first.2
    have whole : lowerArg (.byRef mutability place) le initial = borrowed := by
      simp only [lowerArg, bind_run]
      rfl
    have ghostGrowth : middle.vals.size ≤ next.vals.size := by
      rw [middleReady.roots.valueSize, nextReady.roots.valueSize]
      exact (advB_borrowTo mutability first.1 le first.2 _ _ rfl).vals
    have firstFinalLedger := (placeLedger.underRoot childSource).retained ghostGrowth nextRoots
    dsimp only [le] at whole
    rw [whole]
    refine ⟨next, nextReady, ?_, ?_, firstFinalLedger.trans borrowedLedger, nextSites⟩
    · intro live
      have value := returned live
      refine ⟨value.bound, value.refined, childPath, .place place, before, sourceRoots, after,
        childSource, SourceNodeRoots.place rfl replay, ?_, value.refined⟩
      rw [nextReady.roots.valueSize]
      exact value.bound
    · intro index bound
      have growth : upper.vals.size ≤ middle.vals.size := by
        rw [ready.roots.valueSize, middleReady.roots.valueSize]
        exact (advB_lowerPlace place le initial first.1 first.2 rfl).vals
      exact (nextRoots index (Nat.lt_of_lt_of_le bound growth)).trans (middleRoots index bound)

end Goose.Lower.Validation.ReplacementContentFlowSource
