import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlGraphExtensions
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlIfValue
import Goose.Lower.Validation.ExpressionTypingGenerated
import Goose.Lower.Validation.SummaryPreservationSourceEffectCeiling
import Goose.Lower.Validation.SummaryPreservationReplayNativeIfStages

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

private theorem ifBranchSuffixes {env : PEnv} {root : DemandNode} {func : Func}
    {condition : Expr} {yes no : Core.Block} {le : LEnv} {initial : LS}
    (projects : SourceCanonicalRootFloors.RecipeMetadataProjects env root func (lowerExpr (.ifE condition yes no) le initial).2)
    (continuation : NativeBuilderContinuation func (lowerExpr (.ifE condition yes no) le initial).2)
    (live : (lowerExpr condition le initial).2.cur.isSome = true) :
    let lowered := lowerExpr condition le initial
    let forked := (fork lowered.1 le lowered.2).2
    let yesStart := { forked with cur := some lowered.2.blocks.size }
    let yesResult := lowerBlock none [] true yes le yesStart
    let noStart := { yesResult.2 with cur := some (lowered.2.blocks.size + 1) }
    (SourceCanonicalRootFloors.RecipeMetadataProjects env root func yesResult.2 ∧
      NativeBuilderContinuation func yesResult.2) ∧
      (SourceCanonicalRootFloors.RecipeMetadataProjects env root func (lowerBlock none [] true no le noStart).2 ∧
        NativeBuilderContinuation func (lowerBlock none [] true no le noStart).2) := by
  dsimp only
  let lowered := lowerExpr condition le initial
  let forked := (fork lowered.1 le lowered.2).2
  let yesStart := { forked with cur := some lowered.2.blocks.size }
  let yesResult := lowerBlock none [] true yes le yesStart
  let noStart := { yesResult.2 with cur := some (lowered.2.blocks.size + 1) }
  let noResult := lowerBlock none [] true no le noStart
  let joined := Goose.Lower.joinValue yesResult.2.cur yesResult.1 noResult.2.cur noResult.1 le noResult.2
  obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
  have selected : lowered.2.cur = some block := current
  have whole : lowerExpr (.ifE condition yes no) le initial =
      (joined.1, (recordValueRootRecipe joined.1 (sourceBlockScope yes) le joined.2).2) := by
    apply lowerExpr_ifE_after_branches (rfl : lowerExpr condition le initial = lowered) selected
      (forked := forked) (yesLS := yesResult.2) (noLS := noResult.2)
      (yesBlock := lowered.2.blocks.size) (noBlock := lowered.2.blocks.size + 1)
    · change fork lowered.1 le lowered.2 = ((lowered.2.blocks.size, lowered.2.blocks.size + 1), forked)
      simp only [forked, fork_run _ _ selected]
    · rfl
    · rfl
  rw [whole] at projects
  have joinedProjects := projects.of_advance
    (advB_recordValueRootRecipe joined.1 (sourceBlockScope yes) le joined.2 _ _ rfl)
  have noProjects := joinedProjects.restrict (by
    intro recipe member
    rw [recipesUnchangedB_joinValue]
    exact member)
  have yesProjects : SourceCanonicalRootFloors.RecipeMetadataProjects env root func yesResult.2 :=
    (noProjects.of_advance (advB_lowerBlock none [] true no le noStart _ _ rfl)).restrict
      (by intro recipe member; exact member)
  rw [whole] at continuation
  have joinedContinuation := continuation.of_advance
    (advB_recordValueRootRecipe joined.1 (sourceBlockScope yes) le joined.2 _ _ rfl)
  have noContinuation := joinedContinuation.of_extension
    (joinValue_graphExtension yesResult.2.cur noResult.2.cur yesResult.1 noResult.1 le noResult.2)
  have yesContinuation : NativeBuilderContinuation func yesResult.2 :=
    (noContinuation.of_advance (advB_lowerBlock none [] true no le noStart _ _ rfl)).of_extension
      (graphExtension_sameBlocks rfl)
  exact ⟨⟨yesProjects, yesContinuation⟩, ⟨noProjects, noContinuation⟩⟩

theorem typedIfExpressionOccurrence {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {ls : LS} {upper : Prov}
    {env : TEnv} {penv : PEnv} {siteRoot : DemandNode} {siteTargets : List BlockId} {condition : Expr} {yes no : Core.Block}
    {start finish : Nat} {type : Ty} {before after : RState} {sourceRoots : List RootRef}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (sites : OccurrenceSitesBuilder penv siteRoot siteTargets le ls func vt upper)
    (targetBounds : ReplacementTargetsBound siteTargets ls)
    (source : tyExpr env (.ifE condition yes no) start = .ok (type, finish))
    (replayed : rpExpr penv (.ifE condition yes no) before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerExpr (.ifE condition yes no) le ls).2)
    (environment : ∃ returnTypes, le = lowerEnv env.mod env.vars returnTypes)
    (recipeRoots : ((lowerExpr (.ifE condition yes no) le ls).1, .conditionalScope (sourceBlockScope yes)) ∈
        (lowerExpr (.ifE condition yes no) le ls).2.valueRootRecipes →
      ∀ row ∈ func.roots.values.getD #[], row.1 = (lowerExpr (.ifE condition yes no) le ls).1 →
        row.2 ⊆ refinedResultUpper func sourceRoots ∧
        ∀ actual, GIR.RootsRefine func actual sourceRoots → actual ⊆ row.2)
    (projects : SourceCanonicalRootFloors.RecipeMetadataProjects penv siteRoot func
      (lowerExpr (.ifE condition yes no) le ls).2)
    (continuation : NativeBuilderContinuation func (lowerExpr (.ifE condition yes no) le ls).2)
    (conditionChild : ∀ tn2 roots sourceAfter,
      tyExpr env condition start = .ok (.bool, tn2) →
      rpExpr penv condition before = .ok (roots, sourceAfter) →
      EffectRefinement func sourceAfter.eff target →
      GeneratedBuilderState ls → NativeRows vt (lowerExpr condition le ls).2 →
      SourceCanonicalRootFloors.RecipeMetadataProjects penv siteRoot func (lowerExpr condition le ls).2 →
      NativeBuilderContinuation func (lowerExpr condition le ls).2 →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerExpr condition le ls).2 next ∧
        ((lowerExpr condition le ls).2.cur.isSome = true →
          ReplayValue func next (lowerExpr condition le ls).2
            (lowerExpr condition le ls).1 roots (.data .bool)) ∧
        (∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) ∧
        OccurrenceLedger penv (.expression condition) func vt next ls (lowerExpr condition le ls).2 ∧
        OccurrenceSitesBuilder penv siteRoot siteTargets le (lowerExpr condition le ls).2 func vt next)
    (blockChild : ∀ body, body = yes ∨ body = no → ∀ tn1 tn2 roots range sourceBefore sourceAfter state provenance,
      tyBlock (exprEnv env) [] body tn1 = .ok (type, tn2) →
      rpBlockValue penv [] body sourceBefore = .ok ((roots, range), sourceAfter) →
      EffectRefinement func sourceAfter.eff target →
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      (let lowered := lowerExpr condition le ls
       let forked := (fork lowered.1 le lowered.2).2
       let yesStart := { forked with cur := some lowered.2.blocks.size }
       let yesResult := lowerBlock none [] true yes le yesStart
       (body = yes ∧ state = yesStart) ∨
         (body = no ∧ state = { yesResult.2 with cur := some (lowered.2.blocks.size + 1) })) →
      GeneratedBuilderState state → NativeRows vt (lowerBlock none [] true body le state).2 →
      OccurrenceSitesBuilder penv siteRoot siteTargets le state func vt provenance →
      ReplacementTargetsBound siteTargets state →
      SourceCanonicalRootFloors.RecipeMetadataProjects penv siteRoot func (lowerBlock none [] true body le state).2 →
      NativeBuilderContinuation func (lowerBlock none [] true body le state).2 →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerBlock none [] true body le state).2 next ∧
        ((lowerBlock none [] true body le state).2.cur.isSome = true →
          ReplayValue func next (lowerBlock none [] true body le state).2
            (lowerBlock none [] true body le state).1 roots (.data type)) ∧
        (∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) ∧
        OccurrenceLedger penv (.block body) func vt next state (lowerBlock none [] true body le state).2 ∧
        OccurrenceSitesBuilder penv siteRoot siteTargets le (lowerBlock none [] true body le state).2 func vt next) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.ifE condition yes no) le ls).2 next ∧
      ((lowerExpr (.ifE condition yes no) le ls).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.ifE condition yes no) le ls).2
          (lowerExpr (.ifE condition yes no) le ls).1 sourceRoots (.data type)) ∧
      (∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) ∧
      OccurrenceLedger penv (.expression (.ifE condition yes no)) func vt next ls (lowerExpr (.ifE condition yes no) le ls).2 ∧
      OccurrenceSitesBuilder penv siteRoot siteTargets le (lowerExpr (.ifE condition yes no) le ls).2 func vt next := by
  obtain ⟨conditionCounter, yesCounter, typedCondition, typedYes, typedNo⟩ := tyExpr_ifE_children source
  obtain ⟨conditionRoots, conditionState, yesRoots, yesRange, yesState, noRoots, noRange,
    replayedCondition, replayedYes, replayedNo, _rootUnion⟩ := rpExpr_ifE_children replayed
  have yesEffect := effectRefinement_before_of_replay
    (rp_mono_all.2.2.2.2.1 penv [] no)
    (rp_rebinds_mono_all.2.2.2.2.1 penv [] no)
    (rp_flags_mono_all.2.2.2.2.1 penv [] no) replayedNo wholeEffect
  have conditionEffect := effectRefinement_before_of_replay
    (rp_mono_all.2.2.2.2.1 penv [] yes)
    (rp_rebinds_mono_all.2.2.2.2.1 penv [] yes)
    (rp_flags_mono_all.2.2.2.2.1 penv [] yes) replayedYes yesEffect
  have conditionProjects := projects.of_advance
    (advB_ifE_core (lowerExpr condition le ls).1 (sourceBlockScope yes)
      (advB_lowerBlock none [] true yes) (advB_lowerBlock none [] true no) le
      (lowerExpr condition le ls).2 _ _ rfl)
  have conditionContinuation := continuation.of_advance
    (advB_ifE_core (lowerExpr condition le ls).1 (sourceBlockScope yes)
      (advB_lowerBlock none [] true yes) (advB_lowerBlock none [] true no) le
      (lowerExpr condition le ls).2 _ _ rfl)
  obtain ⟨middle, conditionReady, conditionValue, conditionPrefix, conditionLedger, conditionSites⟩ :=
    conditionChild conditionCounter conditionRoots conditionState typedCondition
      replayedCondition conditionEffect generated (native_if_condition native) conditionProjects conditionContinuation
  let generatedCondition := lowerExpr condition le ls
  have conditionAdvance := advB_lowerExpr condition le ls _ _ rfl
  have conditionAt : DemandNodeAt (.expression (.ifE condition yes no)) [0] (.expression condition) :=
    .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
  have yesAt : DemandNodeAt (.expression (.ifE condition yes no)) [1] (.block yes) :=
    .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
  have noAt : DemandNodeAt (.expression (.ifE condition yes no)) [2] (.block no) :=
    .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
  obtain ⟨next, completed, returned, retained, branchesLedger, finalSites⟩ := ifExpressionOccurrence
    (root := .expression (.ifE condition yes no)) (.data type) conditionReady conditionSites
    (targetBounds.mono conditionAdvance.ext) rfl
    (fun live => (conditionValue live).bound) replayedCondition replayedYes replayedNo replayed
    (by
      intro live actual row reference
      obtain ⟨returnTypes, rfl⟩ := environment
      have typedRow := lowerExpr_generated_typed (.ifE condition yes no) source rfl live generated
      have same : actual = .data type := by simpa only [Option.some.injEq] using row.symm.trans typedRow
      simpa only [same] using reference)
    recipeRoots
    (fun state provenance live stateEq stateReady stateSites stateBounds => by
      obtain ⟨yesGenerated, _noGenerated, yesNative, _noNative⟩ := native_if_branches generated native live
      obtain ⟨branchProjects, branchContinuation⟩ := (ifBranchSuffixes projects continuation live).1
      have childProjects := branchProjects
      rw [← stateEq] at childProjects branchContinuation
      have childGenerated : GeneratedBuilderState state := by rw [stateEq]; exact yesGenerated
      have childNative : NativeRows vt (lowerBlock none [] true yes le state).2 := by rw [stateEq]; exact yesNative
      obtain ⟨next, completed, returned, retained, ledger, finalSites⟩ := blockChild yes (Or.inl rfl) conditionCounter yesCounter yesRoots yesRange conditionState yesState
        state provenance typedYes replayedYes yesEffect stateReady (Or.inl ⟨rfl, stateEq⟩) childGenerated childNative stateSites stateBounds childProjects branchContinuation
      exact ⟨next, completed, returned, retained, ledger.underRoot yesAt, finalSites⟩)
    (fun state provenance live stateEq stateReady stateSites stateBounds => by
      obtain ⟨_yesGenerated, noGenerated, _yesNative, noNative⟩ := native_if_branches generated native live
      obtain ⟨branchProjects, branchContinuation⟩ := (ifBranchSuffixes projects continuation live).2
      have childProjects := branchProjects
      rw [← stateEq] at childProjects branchContinuation
      have childGenerated : GeneratedBuilderState state := by rw [stateEq]; exact noGenerated
      have childNative : NativeRows vt (lowerBlock none [] true no le state).2 := by rw [stateEq]; exact noNative
      obtain ⟨next, completed, returned, retained, ledger, finalSites⟩ := blockChild no (Or.inr rfl) yesCounter finish noRoots noRange yesState after
        state provenance typedNo replayedNo wholeEffect stateReady (Or.inr ⟨rfl, stateEq⟩) childGenerated childNative stateSites stateBounds childProjects branchContinuation
      exact ⟨next, completed, returned, retained, ledger.underRoot noAt, finalSites⟩)

  refine ⟨next, completed, returned, ?_, ?_, finalSites⟩
  · intro index bound
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, conditionReady.roots.valueSize]
      exact conditionAdvance.vals
    exact (retained index (Nat.lt_of_lt_of_le bound growth)).trans (conditionPrefix index bound)
  · have growth : middle.vals.size ≤ next.vals.size := by
      rw [conditionReady.roots.valueSize, completed.roots.valueSize]
      exact (advB_ifE_core generatedCondition.1 (sourceBlockScope yes) (advB_lowerBlock none [] true yes)
        (advB_lowerBlock none [] true no) le generatedCondition.2 _ _ rfl).vals
    exact ((conditionLedger.underRoot conditionAt).retained growth retained).trans branchesLedger

#print axioms typedIfExpressionOccurrence

end Goose.Lower.Validation.ReplacementContentFlowSource
