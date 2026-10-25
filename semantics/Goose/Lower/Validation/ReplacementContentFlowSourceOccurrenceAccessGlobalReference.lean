import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeFrames
import Goose.Lower.Validation.SourceRootShapeReads
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessBorrow
import Goose.Lower.Validation.SummaryPreservationReplayNativeReference
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem occurrenceReplay_global_reference {typingEnv : TEnv} {env : PEnv} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} {place : Place}
    (mutability : Mutability) (tables : SourceRootTables typingEnv env)
    (child : ∀ initial upper, GlobalPlaceOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets place initial upper) :
    ∀ initial upper, GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets (.ref mutability place) initial upper := by
  intro initial upper here type start finish before after sourceRoots typed replayed ceiling ready sites targets generated native metadata continuation
  obtain ⟨info, childFinish, childTyped, shape, _⟩ := tyExpr_ref_place typed
  subst type
  have placeReplay : rpPlace env place before = .ok (sourceRoots, after) := replayed
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let lowered := lowerPlace place le initial
  have childNative := native.of_prefix (types_borrowTo mutability lowered.1 le lowered.2 _ _ rfl)
  have childMetadata := metadata.of_advance (advB_borrowTo mutability lowered.1 le lowered.2 _ _ rfl)
  have childContinuation := continuation.of_advance (advB_borrowTo mutability lowered.1 le lowered.2 _ _ rfl)
  obtain ⟨middle, middleReady, input, retained, ledger, childSites⟩ :=
    child initial upper (accessChildPresent here 0 rfl) info start childFinish before after sourceRoots
      childTyped placeReplay ceiling ready sites targets generated childNative childMetadata childContinuation
  obtain ⟨next, nextReady, value, nextRetained, tailLedger, finalSites⟩ :=
    borrowReferenceOccurrence (root := .expression (.ref mutability place)) mutability info.ty lowered.1 sourceRoots
      middleReady childSites input
  have growth := accessRootsGrowth middleReady nextReady (advB_borrowTo mutability lowered.1 le lowered.2 _ _ rfl).vals
  refine ⟨next, nextReady, value, ?_, ?_, finalSites⟩
  · intro old bound
    have middleBound := Nat.lt_of_lt_of_le bound (accessRootsGrowth ready middleReady
      (advB_lowerPlace place le initial _ _ rfl).vals)
    exact (nextRetained old middleBound).trans (retained old bound)
  · exact ((ledger.retained growth nextRetained).underRoot (accessChildNode 0 rfl)).trans tailLedger

end Goose.Lower.Validation.ReplacementContentFlowSource
