import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessConsumed
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeFrames
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessBounds
import Goose.Lower.Validation.SummaryPreservationReplaySlices

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation ReplacementContentFlowSource

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}

theorem canonical_occurrenceReplay_slice {typingEnv : TEnv} {env : PEnv} {context : ContextId}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId}
    {view : View} {low high : Bound} (mutability : Mutability) (origin : OriginId)
    (source : SourceContextEnvironment typingEnv env context)
    (viewChild : ∀ initial upper, CanonicalViewOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets view initial upper)
    (lowChild : ∀ initial upper, CanonicalBoundOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets low initial upper)
    (highChild : ∀ initial upper, CanonicalBoundOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets high initial upper) :
    ∀ initial upper, CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets
      (.slice mutability view low high origin) initial upper := by
  intro initial upper here cursor type start finish before after roots typed replay ceiling ready sites targets generated native metadata continuation
  have originBound : origin < env.mod.origins.size := by
    obtain ⟨_, _, checked, _⟩ := (st_bind_ok _ _ _ _).mp typed
    have bound := (checkOrg_ok _ _ _ _).mp checked |>.1
    simpa only [← source.tables.moduleEq] using bound
  obtain ⟨element, writable, viewStart, viewFinish, lowFinish, highFinish, viewTyped, lowTyped, highTyped, rfl⟩ :=
    tyExpr_slice_children typed
  obtain ⟨viewRoots, viewAfter, viewReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  obtain ⟨_, lowAfter, lowReplay, tail⟩ := (st_bind_ok _ _ _ _).mp tail
  obtain ⟨_, highAfter, highReplay, _⟩ := (st_bind_ok _ _ _ _).mp tail
  have exactReplay : rpExpr env (.slice mutability view low high origin) before =
      .ok (viewRoots, { highAfter with eff := { highAfter.eff with aborts := true } }) := by
    simp [rpExpr, viewReplay, lowReplay, highReplay, noteAborts, bind, pure, modify,
      Except.bind, Except.pure, StateT.bind, StateT.pure, StateT.modifyGet, modifyGet, MonadStateOf.modifyGet]
  rw [exactReplay] at replay
  cases replay
  have highEffect : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) highAfter.eff target :=
    ⟨ceiling.reads, ceiling.writes, ceiling.grows, ceiling.shrinks, ceiling.rebinds,
      fun _ => ceiling.aborts rfl, ceiling.outputs, ceiling.unknown⟩
  have lowEffect := effectRefinement_before_of_replay
    (rp_mono_all.2.2.2.2.2.2.2.2.2 env high) (rp_rebinds_mono_all.2.2.2.2.2.2.2.2.2 env high)
    (rp_flags_mono_all.2.2.2.2.2.2.2.2.2 env high) highReplay highEffect
  have viewEffect := effectRefinement_before_of_replay
    (rp_mono_all.2.2.2.2.2.2.2.2.2 env low) (rp_rebinds_mono_all.2.2.2.2.2.2.2.2.2 env low)
    (rp_flags_mono_all.2.2.2.2.2.2.2.2.2 env low) lowReplay lowEffect
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let sampled := lowerView view le initial
  let loweredLow := lowerBound low le sampled.2
  let loweredHigh := lowerBound high le loweredLow.2
  have highNative := native.of_prefix (types_emitDef
    (.viewSlice mutability sampled.1 loweredLow.1 loweredHigh.1 (some origin)) le loweredHigh.2 _ _ rfl)
  have lowNative := highNative.of_prefix (types_lowerBound high le loweredLow.2 loweredHigh.1 loweredHigh.2 rfl)
  have viewNative := lowNative.of_prefix (types_lowerBound low le sampled.2 loweredLow.1 loweredLow.2 rfl)
  have highMetadata := metadata.of_advance (advB_emitDef
    (.viewSlice mutability sampled.1 loweredLow.1 loweredHigh.1 (some origin)) le loweredHigh.2 _ _ rfl)
  have highContinuation := continuation.of_advance (advB_emitDef
    (.viewSlice mutability sampled.1 loweredLow.1 loweredHigh.1 (some origin)) le loweredHigh.2 _ _ rfl)
  have lowMetadata := highMetadata.of_advance (advB_lowerBound high le loweredLow.2 loweredHigh.1 loweredHigh.2 rfl)
  have lowContinuation := highContinuation.of_advance (advB_lowerBound high le loweredLow.2 loweredHigh.1 loweredHigh.2 rfl)
  have viewMetadata := lowMetadata.of_advance (advB_lowerBound low le sampled.2 loweredLow.1 loweredLow.2 rfl)
  have viewContinuation := lowContinuation.of_advance (advB_lowerBound low le sampled.2 loweredLow.1 loweredLow.2 rfl)
  obtain ⟨viewUpper, viewReady, viewValue, viewPrefix, viewLedger, viewSites⟩ := viewChild initial upper
    (accessChildPresent here 0 rfl)
    (by obtain ⟨path,located⟩ := cursor; exact ⟨path ++ [0],located.child rfl⟩) (element, writable) viewStart viewFinish before viewAfter
    roots viewTyped viewReplay viewEffect ready sites targets generated viewNative viewMetadata viewContinuation
  obtain ⟨lowUpper, lowReady, lowBounds, lowPrefix, lowLedger, lowSites⟩ := lowChild sampled.2 viewUpper
    (accessChildPresent here 1 rfl)
    (by obtain ⟨path,located⟩ := cursor; exact ⟨path ++ [1],located.child rfl⟩) viewFinish lowFinish viewAfter lowAfter
    lowTyped lowReplay lowEffect viewReady viewSites (targets.mono viewLedger.extension) (generated.lowerView view rfl) lowNative lowMetadata lowContinuation
  obtain ⟨highUpper, highReady, highBounds, highPrefix, highLedger, highSites⟩ := highChild loweredLow.2 lowUpper
    (accessChildPresent here 2 rfl)
    (by obtain ⟨path,located⟩ := cursor; exact ⟨path ++ [2],located.child rfl⟩) lowFinish highFinish lowAfter highAfter
    highTyped highReplay highEffect lowReady lowSites (targets.mono (viewLedger.extension.trans lowLedger.extension)) ((generated.lowerView view rfl).lowerBound low rfl) highNative highMetadata highContinuation
  have lowGrowth := advB_lowerBound low le sampled.2 loweredLow.1 loweredLow.2 rfl
  have highGrowth := advB_lowerBound high le loweredLow.2 loweredHigh.1 loweredHigh.2 rfl
  obtain ⟨next, nextReady, nextValue, nextPrefix⟩ := highReady.slice mutability element viewReplay lowReplay highReplay
    exactReplay ceiling (initial := initial) (viewLS := sampled.2) (lowLS := loweredLow.2) rfl rfl rfl originBound (by
      intro live
      have lowLive := (dead_lowerBound high).live_before (le := le) rfl live
      have viewLive := (dead_lowerBound low).live_before (le := le) rfl lowLive
      have viewBound := (viewValue viewLive).bound
      refine ⟨Nat.lt_of_lt_of_le viewBound (Nat.le_trans lowGrowth.vals highGrowth.vals), ?_, highBounds live, ?_⟩
      · intro value member
        exact Nat.lt_of_lt_of_le (lowBounds lowLive value member) highGrowth.vals
      · rw [highPrefix sampled.1 (by rw [lowReady.roots.valueSize]; exact Nat.lt_of_lt_of_le viewBound lowGrowth.vals),
          lowPrefix sampled.1 (by rw [viewReady.roots.valueSize]; exact viewBound)]
        exact (viewValue viewLive).refined)
  have suffixRun : emitDef (.viewSlice mutability sampled.1 loweredLow.1 loweredHigh.1 (some origin)) le loweredHigh.2 =
      lowerExpr (.slice mutability view low high origin) le initial := rfl
  have nextGrowth := accessRootsGrowth highReady nextReady (adv_emitDef suffixRun).vals
  have lowGhostGrowth := accessRootsGrowth viewReady lowReady lowGrowth.vals
  have highGhostGrowth := accessRootsGrowth lowReady highReady highGrowth.vals
  have suffix : OccurrenceLedger env (.expression (.slice mutability view low high origin))
      (lowerContextAt env.mod env.ctx env.impl) vt next loweredHigh.2
      (lowerExpr (.slice mutability view low high origin) le initial).2 := by
    apply accessEmitDefinition suffixRun
    intro live
    have lowLive := (dead_lowerBound high).live_before (le := le) rfl live
    have viewLive := (dead_lowerBound low).live_before (le := le) rfl lowLive
    refine ⟨?_, ?_, ?_, InstructionOccurrences.no_store (by intros; intro same; cases same), ?_⟩
    · intro address member reference
      simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses,
        List.mem_cons, List.mem_append] at member
      rcases member with viewAddress | lowMember | highMember
      · subst address
        have viewBound : sampled.1 < viewUpper.vals.size := by
          rw [viewReady.roots.valueSize]
          exact (viewValue viewLive).bound
        have lowBound := Nat.lt_of_lt_of_le viewBound lowGhostGrowth
        have highBound := Nat.lt_of_lt_of_le lowBound highGhostGrowth
        apply accessOperandView (accessChildNode 0 rfl) viewReplay (Nat.lt_of_lt_of_le highBound nextGrowth)
        rw [nextPrefix sampled.1 highBound, highPrefix sampled.1 lowBound, lowPrefix sampled.1 viewBound]
        exact (viewValue viewLive).refined
      · have scalar := accessBoundScalar source lowTyped (generated.lowerView view rfl) lowNative lowLive address lowMember
        rw [scalar] at reference
        cases reference
      · have scalar := accessBoundScalar source highTyped ((generated.lowerView view rfl).lowerBound low rfl) highNative live address highMember
        rw [scalar] at reference
        cases reference
    · intro value address same; cases same
    · intro value callee args origin same; cases same
    · intro address member mutability payload reference
      simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses,
        List.mem_cons, List.mem_append] at member
      rcases member with rfl | lowMember | highMember
      · exact False.elim (sourceView_not_reference source.tables viewNative generated viewTyped (rfl : lowerView view le initial = sampled) viewLive mutability payload reference)
      · exact False.elim (nativeScalar_not_reference (accessBoundScalar source lowTyped (generated.lowerView view rfl) lowNative lowLive address lowMember) mutability payload reference)
      · exact False.elim (nativeScalar_not_reference (accessBoundScalar source highTyped ((generated.lowerView view rfl).lowerBound low rfl) highNative live address highMember) mutability payload reference)
  refine ⟨next, nextReady, nextValue, ?_,
    ((((viewLedger.retained lowGhostGrowth lowPrefix).retained highGhostGrowth highPrefix).retained nextGrowth nextPrefix).underRoot
      (accessChildNode 0 rfl)).trans
        ((((lowLedger.retained highGhostGrowth highPrefix).retained nextGrowth nextPrefix).underRoot (accessChildNode 1 rfl)).trans
          (((highLedger.retained nextGrowth nextPrefix).underRoot (accessChildNode 2 rfl)).trans suffix)),
    highSites.emitDef suffixRun nextGrowth nextPrefix⟩
  intro old bound
  have viewGrowth : upper.vals.size ≤ viewUpper.vals.size := by
    rw [ready.roots.valueSize, viewReady.roots.valueSize]
    exact (advB_lowerView view le initial _ _ rfl).vals
  have lowGhostGrowth : viewUpper.vals.size ≤ lowUpper.vals.size := by
    rw [viewReady.roots.valueSize, lowReady.roots.valueSize]
    exact lowGrowth.vals
  have highGhostGrowth : lowUpper.vals.size ≤ highUpper.vals.size := by
    rw [lowReady.roots.valueSize, highReady.roots.valueSize]
    exact highGrowth.vals
  exact (nextPrefix old (Nat.lt_of_lt_of_le bound (Nat.le_trans viewGrowth (Nat.le_trans lowGhostGrowth highGhostGrowth)))).trans
    ((highPrefix old (Nat.lt_of_lt_of_le bound (Nat.le_trans viewGrowth lowGhostGrowth))).trans
      ((lowPrefix old (Nat.lt_of_lt_of_le bound viewGrowth)).trans (viewPrefix old bound)))

#print axioms canonical_occurrenceReplay_slice

end Goose.Lower.Validation.SourceReplacementWriterLedger
