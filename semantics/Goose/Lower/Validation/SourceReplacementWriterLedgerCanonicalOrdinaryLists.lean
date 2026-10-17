import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceListsPrintGlobal
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalOrdinaryContracts

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation ReplacementContentFlowSource

private theorem canonical_typedGlobalExpressionsOccurrenceFromRows
    {ownerRoot : Fragment} {ownerInitial baseline : LS} {typingEnv : TEnv} {env : PEnv}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty}
    {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat}
    {siteRoot : DemandNode} {siteTargets : List BlockId} {anchor parent : DemandNode}
    {initial : LS} {upper : Prov} {expressions : List Expr}
    (step : ∀ expression, expression ∈ expressions → ∀ state provenance,
      CanonicalGlobalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func
        returnTypes slots target scopeCount siteRoot siteTargets expression state provenance)
    (rows : ∀ expression childInitial, some (.expression expression, childInitial) ∈
        expressionChildren (lowerEnv env.mod env.impl.vars returnTypes) expressions initial →
      ∃ path, SourceLoweringAt ownerRoot (lowerEnv env.mod env.impl.vars returnTypes) ownerInitial path
        (.expression expression) childInitial) :
    (rooted : ∃ path, DemandNodeAt siteRoot path anchor) →
    (paths : ∀ expression, expression ∈ expressions →
      ∃ path, DemandNodeAt anchor path (.expression expression)) →
    ∀ types start finish before after,
      tyStructExprs typingEnv types expressions start = .ok ((), finish) →
      rpExprs env expressions before = .ok ((), after) →
      EffectRefinement func after.eff target →
      ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount slots initial upper →
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes) initial func vt upper →
      ReplacementTargetsBound siteTargets initial → GeneratedBuilderState initial →
      NativeRows vt (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
      SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func
        (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
      NativeBuilderContinuation func (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
      ∃ next, ReplayBuilder (lower env.mod) results vt func target
          (lowerEnv env.mod env.impl.vars returnTypes) scopeCount slots
          (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
        ((lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
          ∀ value ∈ (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).1,
            value < (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2.vals.size ∧
            OperandOccurrence env anchor func next value) ∧
        (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
        OccurrenceLedger env anchor func vt next initial
          (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2 ∧
        CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
          (lowerEnv env.mod env.impl.vars returnTypes)
          (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2 func vt next := by
  intro rooted paths types start finish before after typed source wholeEffect ready sites targets generated native metadata continuation
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
          obtain ⟨outerPath, outer⟩ := rooted
          exact ⟨outerPath ++ childPath, sourcePath_append outer childSource⟩
        obtain ⟨childPathAtRoot, childCursor⟩ := rows expression initial (by simp [expressionChildren])
        let lowered := lowerExpr expression le initial
        have tailNative := native.of_prefix (types_lowerExprs rest le lowered.2 _ _ rfl)
        obtain ⟨middle, middleReady, firstValue, middleRoots, firstLedger, middleSites⟩ :=
          step expression (by simp) initial upper childAtSite ⟨childPathAtRoot, childCursor⟩ headType start middleCounter
            before middleSource roots headTyped firstReplay
            firstEffect ready sites targets generated tailNative
            (metadata.of_advance (advB_lowerExprs rest le lowered.2 _ _ rfl))
            (continuation.of_advance (advB_lowerExprs rest le lowered.2 _ _ rfl))
        have restRows : ∀ value childInitial,
            some (.expression value, childInitial) ∈ expressionChildren le rest lowered.2 →
            ∃ path, SourceLoweringAt ownerRoot le ownerInitial path (.expression value) childInitial := by
          intro value childInitial member
          apply rows value childInitial
          change some (.expression value, childInitial) ∈
            some (.expression expression, initial) :: expressionChildren le rest lowered.2
          exact List.mem_cons_of_mem _ member
        obtain ⟨next, nextReady, tailValues, nextRoots, tailLedger, nextSites⟩ :=
          canonical_typedGlobalExpressionsOccurrenceFromRows (parent := parent) (expressions := rest)
            (initial := lowered.2) (upper := middle)
            (fun value member => step value (by simp [member])) restRows
            rooted (fun value member => paths value (by simp [member])) fieldTypes
            middleCounter finish middleSource after tailTyped restReplay wholeEffect middleReady middleSites
            (targets.mono firstLedger.extension) (generated.lowerExpr expression rfl) native metadata continuation
        let tail := lowerExprs rest le lowered.2
        have whole : lowerExprs (expression :: rest) le initial = (lowered.1 :: tail.1, tail.2) := by
          simp only [lowerExprs, bind_run, pure_run]
          rfl
        have valGrowth := (advB_lowerExprs rest le lowered.2 tail.1 tail.2 rfl).vals
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
            have firstLive : lowered.2.cur.isSome = true :=
              (dead_lowerExprs rest).live_before (le := le) (before := lowered.2)
                (after := tail.2) (result := tail.1) rfl live
            have returned := firstValue firstLive
            have occurrence : OperandOccurrence env anchor func middle lowered.1 := by
              refine ⟨childPath, .expression expression, before, roots, middleSource,
                childSource, SourceNodeRoots.expression rfl firstReplay, ?_, returned.refined⟩
              rw [middleReady.roots.valueSize]
              exact returned.bound
            exact ⟨Nat.lt_of_lt_of_le returned.bound valGrowth, occurrence.retained ghostGrowth nextRoots⟩
          · exact tailValues live value member
        · intro index bound
          have growth : upper.vals.size ≤ middle.vals.size := by
            rw [ready.roots.valueSize, middleReady.roots.valueSize]
            exact (advB_lowerExpr expression le initial lowered.1 lowered.2 rfl).vals
          exact (nextRoots index (Nat.lt_of_lt_of_le bound growth)).trans (middleRoots index bound)
      · simp [same, chk] at tailTyped
termination_by expressions.length

theorem canonical_typedGlobalExpressionsOccurrence (parent : Expr) (expressions : List Expr)
    (step : ∀ expression, expression ∈ expressions → ∀ state provenance,
      CanonicalGlobalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func
        returnTypes slots target scopeCount siteRoot siteTargets expression state provenance) :
    ∀ initial upper,
      CanonicalGlobalExpressionsOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func
        returnTypes slots target scopeCount siteRoot siteTargets anchor parent expressions initial upper := by
  intro initial upper rooted cursor shape paths types start finish before after typed source wholeEffect ready sites targets generated native metadata continuation
  obtain ⟨parentPath, parentAt⟩ := cursor
  let le := lowerEnv env.mod env.impl.vars returnTypes
  have rows : ∀ expression childInitial,
      some (.expression expression, childInitial) ∈ expressionChildren le expressions initial →
      ∃ path, SourceLoweringAt ownerRoot le ownerInitial path (.expression expression) childInitial := by
    intro expression childInitial member
    have childMember : some (Fragment.expression expression, childInitial) ∈
        (Fragment.expression parent).children le initial := by
      rw [shape]
      exact member
    exact (SourceLoweringAt.childrenAt parentAt) (.expression expression) childInitial childMember
  exact canonical_typedGlobalExpressionsOccurrenceFromRows (parent := DemandNode.expression parent)
    step rows rooted paths types start finish before after typed source wholeEffect ready sites targets generated native metadata continuation

#print axioms canonical_typedGlobalExpressionsOccurrence

private theorem canonical_typedGlobalPrintArgumentsOccurrenceFromRows
    {ownerRoot : Fragment} {ownerInitial baseline : LS} {typingEnv : TEnv} {env : PEnv}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty}
    {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat}
    {siteRoot : DemandNode} {siteTargets : List BlockId} {anchor : DemandNode}
    {loop : Option LoopCtx} {origin : OriginId} {initial : LS} {upper : Prov}
    {arguments : List PrintArg}
    (step : ∀ expression, .expr expression ∈ arguments → ∀ state provenance,
      CanonicalGlobalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func
        returnTypes slots target scopeCount siteRoot siteTargets expression state provenance)
    (rows : ∀ expression childInitial, some (.expression expression, childInitial) ∈ printChildren
      (lowerEnv env.mod env.impl.vars returnTypes) arguments initial →
      ∃ path, SourceLoweringAt ownerRoot (lowerEnv env.mod env.impl.vars returnTypes) ownerInitial path
        (.expression expression) childInitial) :
    (rooted : ∃ path, DemandNodeAt siteRoot path anchor) →
    (paths : ∀ expression, .expr expression ∈ arguments →
      ∃ path, DemandNodeAt anchor path (.expression expression)) →
    ∀ start finish before after,
      tyPrintArgs typingEnv arguments start = .ok ((), finish) →
      rpPrintArgs env arguments before = .ok ((), after) →
      EffectRefinement func after.eff target →
      ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount slots initial upper →
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes) initial func vt upper →
      ReplacementTargetsBound siteTargets initial → GeneratedBuilderState initial →
      NativeRows vt (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
      SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func
        (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
      NativeBuilderContinuation func (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
      ∃ next, ReplayBuilder (lower env.mod) results vt func target
          (lowerEnv env.mod env.impl.vars returnTypes) scopeCount slots
          (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
        ((lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
          ∀ value ∈ (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).1.flatMap PrintPart.uses,
            value < (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2.vals.size ∧
            OperandOccurrence env anchor func next value) ∧
        (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
        OccurrenceLedger env anchor func vt next initial
          (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 ∧
        CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
          (lowerEnv env.mod env.impl.vars returnTypes)
          (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 func vt next := by
  intro rooted paths start finish before after typed source wholeEffect ready sites targets generated native metadata continuation
  let le := lowerEnv env.mod env.impl.vars returnTypes
  cases arguments with
  | nil =>
    refine ⟨upper, ready, ?_, fun _ _ => rfl, ?_, sites⟩
    · simp [lowerPrintArgs, pure_run]
    · exact EmitsOnly.refl _ _
  | cons argument rest =>
    cases argument with
    | text text =>
      have restRows : ∀ expression childInitial,
          some (.expression expression, childInitial) ∈ printChildren le rest initial →
          ∃ path, SourceLoweringAt ownerRoot le ownerInitial path (.expression expression) childInitial := by
        intro expression childInitial member
        apply rows expression childInitial
        change some (.expression expression, childInitial) ∈ none :: printChildren le rest initial
        exact List.mem_cons_of_mem none member
      obtain ⟨next, completed, values, retained, ledger, nextSites⟩ :=
        canonical_typedGlobalPrintArgumentsOccurrenceFromRows (loop := loop) (origin := origin)
          (arguments := rest) (initial := initial) (upper := upper)
          (fun expression member => step expression (by simp [member])) restRows
          rooted (fun expression member => paths expression (by simp [member]))
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
        obtain ⟨outerPath, outer⟩ := rooted
        exact ⟨outerPath ++ childPath, sourcePath_append outer childSource⟩
      have childCursor : ∃ path, SourceLoweringAt ownerRoot le ownerInitial path (.expression expression) initial := by
        obtain ⟨path, located⟩ := rows expression initial (by simp [printChildren])
        exact ⟨path, located⟩
      let lowered := lowerExpr expression le initial
      have expressionNative := native.of_prefix (types_lowerPrintArgs rest le lowered.2 _ _ rfl)
      obtain ⟨middle, expressionReady, expressionValue, expressionPrefix, expressionLedger, middleSites⟩ :=
        step expression (by simp) initial upper childAtSite childCursor type start middleCounter before middleState roots
          expressionTyped expressionReplay expressionEffect ready sites targets generated expressionNative
          (metadata.of_advance (advB_lowerPrintArgs rest le lowered.2 _ _ rfl))
          (continuation.of_advance (advB_lowerPrintArgs rest le lowered.2 _ _ rfl))
      have restRows : ∀ value childInitial,
          some (.expression value, childInitial) ∈ printChildren le rest lowered.2 →
          ∃ path, SourceLoweringAt ownerRoot le ownerInitial path (.expression value) childInitial := by
        intro value childInitial member
        apply rows value childInitial
        change some (.expression value, childInitial) ∈
          some (.expression expression, initial) :: printChildren le rest lowered.2
        exact List.mem_cons_of_mem _ member
      obtain ⟨next, completed, values, retained, tailLedger, nextSites⟩ :=
        canonical_typedGlobalPrintArgumentsOccurrenceFromRows (loop := loop) (origin := origin)
          (arguments := rest) (initial := lowered.2) (upper := middle)
          (fun value member => step value (by simp [member])) restRows
          rooted (fun value member => paths value (by simp [member]))
          middleCounter finish middleState after tailTyped tailReplay wholeEffect expressionReady middleSites
          (targets.mono expressionLedger.extension) (generated.lowerExpr expression rfl) native metadata continuation
      have valGrowth := (advB_lowerPrintArgs rest le lowered.2 _ _ rfl).vals
      have ghostGrowth : middle.vals.size ≤ next.vals.size := by
        rw [expressionReady.roots.valueSize, completed.roots.valueSize]
        exact valGrowth
      have firstFinalLedger := (expressionLedger.underRoot childSource).retained ghostGrowth retained
      have whole : lowerPrintArgs (.expr expression :: rest) le initial =
          (PrintPart.val lowered.1 :: (lowerPrintArgs rest le lowered.2).1, (lowerPrintArgs rest le lowered.2).2) := by
        simp only [lowerPrintArgs, bind_run, pure_run]
        rfl
      dsimp only [le] at whole
      rw [whole]
      refine ⟨next, completed, ?_, ?_, firstFinalLedger.trans tailLedger, nextSites⟩
      · intro live value member
        simp only [List.flatMap_cons, PrintPart.uses, List.singleton_append, List.mem_cons] at member
        rcases member with equal | tailMember
        · subst value
          have childLive : lowered.2.cur.isSome = true := by
            cases current : lowered.2.cur with
            | some block => rfl
            | none =>
              change (lowerPrintArgs rest le lowered.2).2.cur.isSome = true at live
              have liveBefore := (dead_lowerPrintArgs rest).live_before rfl live
              rw [current] at liveBefore
              cases liveBefore
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

theorem canonical_typedGlobalPrintArgumentsOccurrence
    {ownerRoot : Fragment} {ownerInitial baseline : LS} {typingEnv : TEnv} {env : PEnv}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty}
    {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat}
    {siteRoot : DemandNode} {siteTargets : List BlockId} {anchor : DemandNode}
    {loop : Option LoopCtx} {origin : OriginId} (arguments : List PrintArg)
    (step : ∀ expression, .expr expression ∈ arguments → ∀ state provenance,
      CanonicalGlobalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func
        returnTypes slots target scopeCount siteRoot siteTargets expression state provenance) :
    ∀ initial upper,
      CanonicalGlobalPrintArgumentsOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func
        returnTypes slots target scopeCount siteRoot siteTargets anchor loop origin arguments initial upper := by
  intro initial upper rooted cursor paths start finish before after typed source wholeEffect ready sites targets generated native metadata continuation
  obtain ⟨parentPath, parent⟩ := cursor
  let le := lowerEnv env.mod env.impl.vars returnTypes
  have rows : ∀ expression childInitial,
      some (.expression expression, childInitial) ∈ printChildren le arguments initial →
      ∃ path, SourceLoweringAt ownerRoot le ownerInitial path (.expression expression) childInitial := by
    intro expression childInitial member
    have childMember : some (Fragment.expression expression, childInitial) ∈
        (Fragment.statement loop (.print arguments origin)).children le initial := by
      change some (Fragment.expression expression, childInitial) ∈ printChildren le arguments initial
      exact member
    exact (SourceLoweringAt.childrenAt parent) (.expression expression) childInitial childMember
  exact canonical_typedGlobalPrintArgumentsOccurrenceFromRows (loop := loop) (origin := origin) step rows rooted paths
    start finish before after typed source wholeEffect ready sites targets generated native metadata continuation

#print axioms canonical_typedGlobalPrintArgumentsOccurrence

end Goose.Lower.Validation.SourceReplacementWriterLedger
