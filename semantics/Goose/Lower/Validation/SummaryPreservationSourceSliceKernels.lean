import Goose.Lower.Validation.SummaryPreservationSourceBoundContracts
import Goose.Lower.Validation.SummaryPreservationReplaySlices
import Goose.Lower.Validation.SourceRootShapeReads
import Goose.Lower.Validation.SourceSymbolRefs

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}

theorem expressionReplay_slice {view : View} {low high : Bound} (mutability : Mutability) (origin : OriginId)
    (tables : SourceRootTables typingEnv env)
    (viewChild : ViewReplayAt typingEnv env results vt target scopeCount view initial upper)
    (lowChild : ∀ provenance, BoundReplayAt typingEnv env results vt target scopeCount low
      (lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 provenance)
    (highChild : ∀ provenance, BoundReplayAt typingEnv env results vt target scopeCount high
      (lowerBound low (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerView view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2).2 provenance) :
    ExpressionReplayAt typingEnv env results vt target scopeCount (.slice mutability view low high origin) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  have originBound : origin < env.mod.origins.size := by
    simpa only [← tables.moduleEq] using Core.tyExpr_slice_success_origin_bound typed
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
  obtain ⟨viewUpper, viewReady, viewValue, viewPrefix⟩ := viewChild (element, writable) viewStart viewFinish before viewAfter
    roots viewTyped viewReplay viewEffect ready generated viewNative
  obtain ⟨lowUpper, lowReady, lowBounds, lowPrefix⟩ := lowChild viewUpper viewFinish lowFinish viewAfter lowAfter
    lowTyped lowReplay lowEffect viewReady (generated.lowerView view rfl) lowNative
  obtain ⟨highUpper, highReady, highBounds, highPrefix⟩ := highChild lowUpper lowFinish highFinish lowAfter highAfter
    highTyped highReplay highEffect lowReady ((generated.lowerView view rfl).lowerBound low rfl) highNative
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
  refine ⟨next, nextReady, nextValue, ?_⟩
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

#print axioms expressionReplay_slice

end Goose.Lower.Validation.SummaryPreservation
