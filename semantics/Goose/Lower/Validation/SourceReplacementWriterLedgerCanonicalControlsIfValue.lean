import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlFrames
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeSteps
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeValue
import Goose.Lower.Validation.JoinContentsGraph
import Goose.Lower.Validation.SummaryPreservationReplayJoin
import Goose.Lower.Validation.SummaryPreservationReplayLoopsBuilder
import Goose.Lower.Validation.SummaryPreservationReplayIfSource

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open ReplacementContentFlowSource Goose.Core Goose.GIR SummaryPreservation

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}


private theorem canonical_joinValue_value_growth {le : LEnv} {before after : LS} {result : ValueId}
    {yes no : Option BlockId} {yesValue noValue : ValueId}
    (run : Goose.Lower.joinValue yes yesValue no noValue le before = (result, after)) :
    before.vals.size ≤ after.vals.size := by
  unfold Goose.Lower.joinValue at run
  cases yes <;> cases no
  · simp only [bind_eq] at run
    obtain ⟨_, middle, selected, done⟩ := run
    rw [setCur_run] at selected
    obtain ⟨_, rfl⟩ := Prod.mk.inj selected
    obtain ⟨_, rfl⟩ := pure_eq.mp done
    exact Nat.le_refl _
  all_goals
    simp only [bind_eq] at run
    obtain ⟨type, middle, typeRun, ⟨block, parameters⟩, allocated, allocation,
      _, patched, patch, _, resumed, resume, done⟩ := run
    have sameMiddle : middle = before :=
      (congrArg Prod.snd typeRun).symm.trans (valTy_run _ le before)
    subst middle
    rw [newBlock1_run] at allocation
    obtain ⟨_, rfl⟩ := Prod.mk.inj allocation
    rw [setCur_run] at resume
    obtain ⟨_, rfl⟩ := Prod.mk.inj resume
    obtain ⟨_, rfl⟩ := pure_eq.mp done
    have values := patchBrs_values _ patch
    change before.vals.size ≤ patched.vals.size
    rw [values]
    simp

theorem canonical_ifExpressionOccurrence {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {initial ls : LS} {upper : Prov}
    {env : PEnv} {root siteRoot : DemandNode} {siteTargets : List BlockId} {condition : Expr} {yes no : Core.Block} {conditionValue : ValueId}
    {initialSource conditionState yesState after : RState}
    {conditionRoots yesRoots noRoots sourceRoots : List RootRef} {yesRange noRange : Nat × Nat}
    (type : VTy)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (sites : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le ls func vt upper)
    (targetBounds : ReplacementTargetsBound siteTargets ls)
    (conditionRun : lowerExpr condition le initial = (conditionValue, ls))
    (conditionBound : ls.cur.isSome = true → conditionValue < ls.vals.size)
    (conditionReplay : rpExpr env condition initialSource = .ok (conditionRoots, conditionState))
    (yesReplay : rpBlockValue env [] yes conditionState = .ok ((yesRoots, yesRange), yesState))
    (noReplay : rpBlockValue env [] no yesState = .ok ((noRoots, noRange), after))
    (source : rpExpr env (.ifE condition yes no) initialSource = .ok (sourceRoots, after))
    (resultType : (lowerExpr (.ifE condition yes no) le initial).2.cur.isSome = true → ∀ actual,
      (lowerExpr (.ifE condition yes no) le initial).2.vals[(lowerExpr (.ifE condition yes no) le initial).1]? =
        some (some actual) → actual.refLike = true → type.refLike = true)
    (recipeRoots : ((lowerExpr (.ifE condition yes no) le initial).1, .conditionalScope (sourceBlockScope yes)) ∈
        (lowerExpr (.ifE condition yes no) le initial).2.valueRootRecipes →
      ∀ row ∈ func.roots.values.getD #[], row.1 = (lowerExpr (.ifE condition yes no) le initial).1 →
        row.2 ⊆ refinedResultUpper func sourceRoots ∧
        ∀ actual, GIR.RootsRefine func actual sourceRoots → actual ⊆ row.2)
    (yesChild : ∀ state provenance, ls.cur.isSome = true →
      state = { (fork conditionValue le ls).2 with cur := some ls.blocks.size } →
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le state func vt provenance →
      ReplacementTargetsBound siteTargets state →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerBlock none [] true yes le state).2 next ∧
        ((lowerBlock none [] true yes le state).2.cur.isSome = true →
          ReplayValue func next (lowerBlock none [] true yes le state).2
            (lowerBlock none [] true yes le state).1 yesRoots type) ∧
        (∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) ∧
        OccurrenceLedger env root func vt next state (lowerBlock none [] true yes le state).2 ∧
        CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le (lowerBlock none [] true yes le state).2 func vt next)
    (noChild : ∀ state provenance, ls.cur.isSome = true →
      state = { (lowerBlock none [] true yes le
        { (fork conditionValue le ls).2 with cur := some ls.blocks.size }).2 with
          cur := some (ls.blocks.size + 1) } →
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le state func vt provenance →
      ReplacementTargetsBound siteTargets state →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerBlock none [] true no le state).2 next ∧
        ((lowerBlock none [] true no le state).2.cur.isSome = true →
          ReplayValue func next (lowerBlock none [] true no le state).2
            (lowerBlock none [] true no le state).1 noRoots type) ∧
        (∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) ∧
        OccurrenceLedger env root func vt next state (lowerBlock none [] true no le state).2 ∧
        CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le (lowerBlock none [] true no le state).2 func vt next) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.ifE condition yes no) le initial).2 next ∧
      ((lowerExpr (.ifE condition yes no) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.ifE condition yes no) le initial).2
          (lowerExpr (.ifE condition yes no) le initial).1 sourceRoots type) ∧
      (∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) ∧
      OccurrenceLedger env root func vt next ls (lowerExpr (.ifE condition yes no) le initial).2 ∧
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le (lowerExpr (.ifE condition yes no) le initial).2 func vt next := by
  rw [rpExpr_ifE_after_branches conditionReplay yesReplay noReplay] at source
  cases source
  cases current : ls.cur with
  | none =>
    have stopped : lowerExpr (.ifE condition yes no) le initial = (0, ls) := by
      simp only [lowerExpr, bind_run, conditionRun, whenLive_none _ _ _ current]
    rw [stopped]
    exact ⟨upper, ready, by simp [current], (fun _ _ => rfl), .refl _ _, sites⟩
  | some block =>
    let forked := (fork conditionValue le ls).2
    let yesStart := { forked with cur := some ls.blocks.size }
    have forkReady := ready.loopFork conditionValue (conditionBound (by simp [current]))
    have forkSize : forked.blocks.size = ls.blocks.size + 2 := by
      simp [forked, fork_run _ _ current]
    have yesReady : ReplayBuilder module results vt func target le scopeCount slots yesStart upper := by
      have selected := forkReady.setCur (some ls.blocks.size) (by
        intro candidate row
        have same : candidate = ls.blocks.size := (Option.some.inj row).symm
        subst candidate
        change ls.blocks.size < forked.blocks.size
        rw [forkSize]
        omega)
      simpa only [setCur_run] using selected
    have yesSites : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le yesStart func vt upper :=
      (sites.fork conditionValue).setCur _
    have yesBounds : ReplacementTargetsBound siteTargets yesStart := by
      intro target member
      exact Nat.lt_of_lt_of_le (targetBounds target member) (by change ls.blocks.size ≤ forked.blocks.size; rw [forkSize]; omega)
    obtain ⟨middle, yesCompleted, yesValue, yesPrefix, yesLedger, yesSites⟩ :=
      yesChild yesStart upper (by simp [current]) rfl yesReady yesSites yesBounds
    let yesResult := lowerBlock none [] true yes le yesStart
    have yesGrowth := advB_lowerBlock none [] true yes le yesStart yesResult.1 yesResult.2 rfl
    let noStart := { yesResult.2 with cur := some (ls.blocks.size + 1) }
    have noReady : ReplayBuilder module results vt func target le scopeCount slots noStart middle := by
      have selected := yesCompleted.setCur (some (ls.blocks.size + 1)) (by
        intro candidate row
        cases row
        apply Nat.lt_of_lt_of_le (m := yesStart.blocks.size) _ yesGrowth.ext.1
        change ls.blocks.size + 1 < forked.blocks.size
        rw [forkSize]
        omega)
      simpa only [setCur_run] using selected
    have noSites := yesSites.setCur (some (ls.blocks.size + 1))
    have noBounds : ReplacementTargetsBound siteTargets noStart := yesBounds.mono yesGrowth.ext
    obtain ⟨next, noCompleted, noValue, noPrefix, noLedger, noSites⟩ :=
      noChild noStart middle (by simp [current]) rfl noReady noSites noBounds
    let noResult := lowerBlock none [] true no le noStart
    have noGrowth := advB_lowerBlock none [] true no le noStart noResult.1 noResult.2 rfl
    have firstBound (reachable : yesResult.2.cur.isSome = true) : yesResult.1 < noResult.2.vals.size :=
      Nat.lt_of_lt_of_le (yesValue reachable).bound noGrowth.vals
    have firstRoots (reachable : yesResult.2.cur.isSome = true) :
        rootsAt next.vals yesResult.1 = rootsAt middle.vals yesResult.1 :=
      noPrefix yesResult.1 (by rw [yesCompleted.roots.valueSize]; exact (yesValue reachable).bound)
    obtain ⟨finalUpper, completed, returned, retained, ceiling⟩ := noCompleted.joinValueWithCeiling
      (unionRoots yesRoots noRoots) type
      (fun destination row => ⟨Nat.lt_of_lt_of_le (yesCompleted.current destination row) noGrowth.ext.1,
        firstBound (by change (lowerBlock none [] true yes le yesStart).2.cur.isSome = true; rw [row]; rfl)⟩)
      (fun destination row => ⟨noCompleted.current destination row, (noValue (by simp [row])).bound⟩)
      (fun reachable => by
        rw [firstRoots reachable]
        exact (yesValue reachable).refined.source_mono
          (fun root member => mem_unionRoots_iff.mpr (Or.inl member)))
      (fun reachable => (noValue reachable).refined.source_mono
        (fun root member => mem_unionRoots_iff.mpr (Or.inr member)))
      (fun nonref reachable => by rw [firstRoots reachable]; exact (yesValue reachable).scalar nonref)
      (fun nonref reachable => (noValue reachable).scalar nonref)
      (value := (Goose.Lower.joinValue yesResult.2.cur yesResult.1 noResult.2.cur noResult.1 le noResult.2).1)
      (final := (Goose.Lower.joinValue yesResult.2.cur yesResult.1 noResult.2.cur noResult.1 le noResult.2).2) rfl
    let joined := Goose.Lower.joinValue yesResult.2.cur yesResult.1 noResult.2.cur noResult.1 le noResult.2
    let recorded := (Goose.Lower.recordValueRootRecipe joined.1 (sourceBlockScope yes) le joined.2).2
    have whole : lowerExpr (.ifE condition yes no) le initial = (joined.1, recorded) := by
      apply lowerExpr_ifE_after_branches conditionRun current
        (forked := forked) (yesBlock := ls.blocks.size) (noBlock := ls.blocks.size + 1)
        (yesValue := yesResult.1) (noValue := noResult.1) (yesLS := yesResult.2) (noLS := noResult.2)
      · simp only [forked, fork_run _ _ current]
      · rfl
      · rfl
    have recordedFrame : recorded.blocks = joined.2.blocks ∧ recorded.vals = joined.2.vals ∧
        recorded.cur = joined.2.cur := by
      dsimp only [recorded]
      rw [recordValueRootRecipe_run]
      exact ⟨rfl, rfl, rfl⟩
    have recordedReady : ReplayBuilder module results vt func target le scopeCount slots recorded finalUpper :=
      completed.recordSourceValueRecipe joined.1 (sourceBlockScope yes) (unionRoots yesRoots noRoots) type ceiling
        (by
          intro live actual row reference
          apply resultType (by simpa only [whole, recordedFrame.2.2] using live) actual ?_ reference
          simpa only [whole, recordedFrame.2.1] using row)
        (fun live => (returned live).refined)
        (by
          intro event row member same
          apply recipeRoots ?_ row member ?_
          · rw [whole]
            change (joined.1, .conditionalScope (sourceBlockScope yes)) ∈
              (Goose.Lower.recordValueRootRecipe joined.1 (sourceBlockScope yes) le joined.2).2.valueRootRecipes
            rw [event]
            simp
          · simpa only [whole] using same)
    have recordedReturned : recorded.cur.isSome = true →
        ReplayValue func finalUpper recorded joined.1 (unionRoots yesRoots noRoots) type := by
      intro live
      have priorLive : joined.2.cur.isSome = true := by rwa [← recordedFrame.2.2]
      have previous := returned priorLive
      exact ⟨by rw [recordedFrame.2.1]; exact previous.bound, previous.refined, previous.scalar⟩
    rw [whole]
    refine ⟨finalUpper, recordedReady, recordedReturned, ?_, ?_, ?_⟩
    · intro index bound
      have middleGrowth : upper.vals.size ≤ middle.vals.size := by
        rw [yesReady.roots.valueSize, yesCompleted.roots.valueSize]
        exact yesGrowth.vals
      have nextGrowth : middle.vals.size ≤ next.vals.size := by
        rw [noReady.roots.valueSize, noCompleted.roots.valueSize]
        exact noGrowth.vals
      exact (retained index (Nat.lt_of_lt_of_le bound (Nat.le_trans middleGrowth nextGrowth))).trans
        ((noPrefix index (Nat.lt_of_lt_of_le bound middleGrowth)).trans (yesPrefix index bound))
    · have noGrowthGhost : middle.vals.size ≤ next.vals.size := by
        rw [yesCompleted.roots.valueSize, noCompleted.roots.valueSize]
        exact noGrowth.vals
      have joinedGrowth : next.vals.size ≤ finalUpper.vals.size := by
        rw [noCompleted.roots.valueSize, completed.roots.valueSize]
        exact canonical_joinValue_value_growth (le := le) (before := noResult.2) rfl
      have startedLedger : OccurrenceLedger env root func vt middle ls yesStart :=
        (occurrenceLedger_fork conditionValue le ls _ _ rfl).trans (.of_blocks rfl)
      have throughYes : OccurrenceLedger env root func vt middle ls yesResult.2 := startedLedger.trans yesLedger
      have selectedLedger : OccurrenceLedger env root func vt next yesResult.2 noStart := .of_blocks rfl
      have throughNo : OccurrenceLedger env root func vt next ls noResult.2 :=
        ((throughYes.retained noGrowthGhost noPrefix).trans selectedLedger).trans noLedger
      have joinedLedger : OccurrenceLedger env root func vt finalUpper noResult.2 joined.2 :=
        emitsOnly_joinValue _ occurrenceInstructionTerm _ _ _ _ le noResult.2 _ _ rfl
      exact ((throughNo.retained joinedGrowth retained).trans joinedLedger).trans (.of_blocks recordedFrame.1)
    · have joinedSites : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le joined.2 func vt finalUpper := by
        apply noSites.of_action (emitsOnly_joinValue _ (fun _ => trivial) _ _ _ _)
          (types_joinValue _ _ _ _) (generatedTargetFrame_joinValue none _ _ _ _) rfl
        · rw [noCompleted.roots.valueSize, completed.roots.valueSize]
          exact canonical_joinValue_value_growth (le := le) (before := noResult.2) rfl
        · exact retained
      exact joinedSites.recordValueRootRecipe joined.1 (sourceBlockScope yes)

#print axioms canonical_ifExpressionOccurrence

end Goose.Lower.Validation.SourceReplacementWriterLedger
