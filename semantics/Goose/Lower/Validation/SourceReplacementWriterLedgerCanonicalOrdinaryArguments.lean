import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsGlobal
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsBorrow
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalOrdinaryArgumentsContracts
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation ReplacementContentFlowSource

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}
  {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty}
  {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat}
  {siteRoot anchor : DemandNode} {siteTargets : List BlockId}

theorem canonical_typedGlobalArgumentOccurrence (argument : Arg)
    (expressionChild : ∀ expression, argument = .byVal expression → ∀ state provenance,
      CanonicalGlobalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func
        returnTypes slots target scopeCount siteRoot siteTargets expression state provenance)
    (placeChild : ∀ mutability place, argument = .byRef mutability place → ∀ state provenance,
      CanonicalGlobalPlaceOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func
        returnTypes slots target scopeCount siteRoot siteTargets place state provenance) :
    ∀ initial upper, CanonicalGlobalArgumentOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt
      func returnTypes slots target scopeCount siteRoot siteTargets anchor argument initial upper := by
  intro initial upper anchored path actual start finish before after sourceRoots typed replay wholeEffect
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
      expressionChild expression rfl initial upper childAtSite actual type start finish before after sourceRoots
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
    let lowered := lowerPlace place le initial
    have placeNative := native.of_prefix
      (types_borrowTo mutability lowered.1 le lowered.2 _ _ rfl)
    obtain ⟨middle, middleReady, address, middleRoots, placeLedger, middleSites⟩ :=
      placeChild mutability place rfl initial upper childAtSite actual info start finish before after sourceRoots
        typed replay wholeEffect ready sites targets generated placeNative
        (metadata.of_advance (advB_borrowTo mutability lowered.1 le lowered.2 _ _ rfl))
        (continuation.of_advance (advB_borrowTo mutability lowered.1 le lowered.2 _ _ rfl))
    obtain ⟨next, nextReady, returned, nextRoots, borrowedLedger, _borrowedSites, physical⟩ :=
      argumentBorrowOccurrence (root := anchor) mutability Ty.unit lowered.1 sourceRoots middleReady
        middleSites.toOld address
    let borrowed := borrowTo mutability lowered.1 le lowered.2
    have whole : lowerArg (.byRef mutability place) le initial = borrowed := by
      simp only [lowerArg, bind_run]
      rfl
    have ghostGrowth : middle.vals.size ≤ next.vals.size := by
      rw [middleReady.roots.valueSize, nextReady.roots.valueSize]
      exact (advB_borrowTo mutability lowered.1 le lowered.2 _ _ rfl).vals
    have emitted : EmitsOnly NotReplacement lowered.2 borrowed.2 :=
      accessBorrowEmits rfl (fun _ => trivial) (fun _ => trivial)
    have nextSites := middleSites.of_emits emitted
      (types_borrowTo mutability lowered.1 le lowered.2 _ _ rfl)
      (.of_run (generatedTargetFrame_borrowTo none mutability lowered.1) rfl)
      ghostGrowth nextRoots
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
        exact (advB_lowerPlace place le initial lowered.1 lowered.2 rfl).vals
      exact (nextRoots index (Nat.lt_of_lt_of_le bound growth)).trans (middleRoots index bound)

#print axioms canonical_typedGlobalArgumentOccurrence

end Goose.Lower.Validation.SourceReplacementWriterLedger
