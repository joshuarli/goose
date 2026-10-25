import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceListsGlobalContracts
import Goose.Lower.Validation.ExpressionTypingAggregateOps

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty}
  {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat}
  {siteRoot anchor : DemandNode} {siteTargets : List BlockId}

theorem typedGlobalExpressionsOccurrence (expressions : List Expr)
    (step : ∀ expression ∈ expressions, ∀ state provenance,
      GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
        expression state provenance) :
    ∀ initial upper, GlobalExpressionsOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount
      siteRoot siteTargets anchor expressions initial upper := by
  intro initial upper anchored paths types start finish before after typed source wholeEffect
    ready sites targets generated native metadata continuation
  let le := lowerEnv env.mod env.impl.vars returnTypes
  cases expressions with
  | nil =>
    refine ⟨upper, ready, ?_, fun _ _ => rfl, ?_, sites⟩
    · simp only [lowerExprs, pure_run, List.not_mem_nil, false_implies, implies_true]
    · exact EmitsOnly.refl _ _
  | cons expression rest =>
    cases types with
    | nil => exact ((rej_ok _ _ _ _).mp typed).elim
    | cons fieldType fieldTypes =>
      simp only [tyStructExprs] at typed
      obtain ⟨headType, middleCounter, headTyped, tailTyped⟩ := (st_bind_ok _ _ _ _).mp typed
      by_cases same : (headType == fieldType) = true
      · simp only [same, ite_true] at tailTyped
        obtain ⟨roots, middleSource, firstReplay, restReplay⟩ := (st_bind_ok _ _ _ _).mp source
        have firstEffect := effectRefinement_before_of_replay
          (rp_mono_all.2.2.2.1 env rest) (rp_rebinds_mono_all.2.2.2.1 env rest)
          (rp_flags_mono_all.2.2.2.1 env rest) restReplay wholeEffect
        obtain ⟨childPath, childSource⟩ := paths expression (by simp)
        have childAtSite : ∃ path, DemandNodeAt siteRoot path (.expression expression) := by
          obtain ⟨outerPath, outer⟩ := anchored
          exact ⟨outerPath ++ childPath, sourcePath_append outer childSource⟩
        have headNative := native.of_prefix (types_lowerExprs rest le (lowerExpr expression le initial).2 _ _ rfl)
        obtain ⟨middle, middleReady, firstValue, middleRoots, firstLedger, middleSites⟩ :=
          step expression (by simp) initial upper childAtSite headType start middleCounter before middleSource roots
            headTyped firstReplay firstEffect ready sites targets generated headNative
            (metadata.of_advance (advB_lowerExprs rest le (lowerExpr expression le initial).2 _ _ rfl))
            (continuation.of_advance (advB_lowerExprs rest le (lowerExpr expression le initial).2 _ _ rfl))
        obtain ⟨next, nextReady, tailValues, nextRoots, tailLedger, nextSites⟩ :=
          typedGlobalExpressionsOccurrence rest (fun child member => step child (by simp [member]))
            (lowerExpr expression le initial).2 middle anchored
            (fun child member => paths child (by simp [member])) fieldTypes middleCounter finish middleSource after
            tailTyped restReplay wholeEffect middleReady middleSites (targets.mono firstLedger.extension)
            (generated.lowerExpr expression rfl) native metadata continuation
        let first := lowerExpr expression le initial
        let tail := lowerExprs rest le first.2
        have whole : lowerExprs (expression :: rest) le initial = (first.1 :: tail.1, tail.2) := by
          simp only [lowerExprs, bind_run, pure_run]
          rfl
        have valGrowth := (advB_lowerExprs rest le first.2 tail.1 tail.2 rfl).vals
        have ghostGrowth : middle.vals.size ≤ next.vals.size := by
          rw [middleReady.roots.valueSize, nextReady.roots.valueSize]
          exact valGrowth
        have firstFinalLedger := (firstLedger.underRoot childSource).retained ghostGrowth nextRoots
        dsimp only [le] at whole
        rw [whole]
        refine ⟨next, nextReady, ?_, ?_, firstFinalLedger.trans tailLedger, nextSites⟩
        · intro live value member
          rcases List.mem_cons.mp member with equal | member
          · subst value
            have firstLive : first.2.cur.isSome = true :=
              (dead_lowerExprs rest).live_before (le := le) (before := first.2)
                (after := tail.2) (result := tail.1) rfl live
            have returned := firstValue firstLive
            have origin : OperandOccurrence env anchor func middle first.1 := by
              refine ⟨childPath, .expression expression, before, roots, middleSource,
                childSource, SourceNodeRoots.expression rfl firstReplay, ?_, returned.refined⟩
              rw [middleReady.roots.valueSize]
              exact returned.bound
            exact ⟨Nat.lt_of_lt_of_le returned.bound valGrowth, origin.retained ghostGrowth nextRoots⟩
          · exact tailValues live value member
        · intro index bound
          have growth : upper.vals.size ≤ middle.vals.size := by
            rw [ready.roots.valueSize, middleReady.roots.valueSize]
            exact (advB_lowerExpr expression le initial first.1 first.2 rfl).vals
          exact (nextRoots index (Nat.lt_of_lt_of_le bound growth)).trans (middleRoots index bound)
      · simp [same, chk] at tailTyped
termination_by expressions.length

theorem typedGlobalExpressionsAsOccurrence (expressions : List Expr)
    (step : ∀ expression ∈ expressions, ∀ state provenance,
      GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
        expression state provenance)
    (initial : LS) (upper : Prov) (anchored : ∃ path, DemandNodeAt siteRoot path anchor)
    (paths : ∀ expression ∈ expressions, ∃ path, DemandNodeAt anchor path (.expression expression))
    (element : Ty) (start finish : Nat) (before after : RState)
    (typed : tyExprsAs typingEnv element expressions start = .ok ((), finish)) :
    rpExprs env expressions before = .ok ((), after) →
    EffectRefinement func after.eff target →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars returnTypes) initial
      func vt upper →
    ReplacementTargetsBound siteTargets initial → GeneratedBuilderState initial →
    NativeRows vt (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func
      (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    NativeBuilderContinuation func
      (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      ((lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
        ∀ value ∈ (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).1,
          value < (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2.vals.size ∧
          OperandOccurrence env anchor func next value) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env anchor func vt next initial
        (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2
        func vt next :=
  typedGlobalExpressionsOccurrence expressions step initial upper anchored paths
    (List.replicate expressions.length element) start finish before after (tyExprsAs_structExprs typed)

end Goose.Lower.Validation.ReplacementContentFlowSource
