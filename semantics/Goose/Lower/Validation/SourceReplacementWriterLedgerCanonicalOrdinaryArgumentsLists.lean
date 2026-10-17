import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsPhysicalLists
import Goose.Lower.Validation.SourceRootShapeReads
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalOrdinaryArguments

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation ReplacementContentFlowSource

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}
  {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty}
  {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat}
  {siteRoot anchor : DemandNode} {siteTargets : List BlockId}

theorem canonical_typedEmptyPhysicalArgumentOccurrence
    (tables : SourceRootTables typingEnv env) (empty : typingEnv.vars = #[]) (argument : Arg)
    (expressionChild : ∀ expression, argument = .byVal expression → ∀ state provenance,
      CanonicalGlobalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func
        returnTypes slots target scopeCount siteRoot siteTargets expression state provenance)
    (placeChild : ∀ mutability place, argument = .byRef mutability place → ∀ state provenance,
      CanonicalGlobalPlaceOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func
        returnTypes slots target scopeCount siteRoot siteTargets place state provenance) :
    ∀ initial upper, CanonicalPhysicalArgumentOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt
      func returnTypes slots target scopeCount siteRoot siteTargets anchor argument initial upper := by
  intro initial upper rooted path actual start finish before after sourceRoots typed replay wholeEffect
    ready sites targets generated native metadata continuation
  obtain ⟨next, completed, returned, retained, ledger, nextSites⟩ :=
    canonical_typedGlobalArgumentOccurrence argument expressionChild placeChild initial upper
      rooted path actual start finish before after sourceRoots typed replay wholeEffect ready sites targets generated native
      metadata continuation
  refine ⟨next, completed, returned, retained, ledger, nextSites, ?_⟩
  intro live mutability place same shaped
  cases same
  obtain ⟨info, placeTyped⟩ := typed
  obtain ⟨index, localPlace | ⟨contents, reference⟩⟩ := shaped
  · subst place
    have bound := Core.tyPlace_var_success_bound placeTyped
    simp [empty] at bound
  · simp [PEnv.isRefSliceVar, tables.variablesEq, empty] at reference

private theorem canonical_typedPhysicalArgumentsOccurrenceFromRows
    (arguments : List Arg) (initial : LS)
    (step : ∀ argument, argument ∈ arguments → ∀ initial upper,
      CanonicalPhysicalArgumentOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func
        returnTypes slots target scopeCount siteRoot siteTargets anchor argument initial upper)
    (rows : ∀ argument childInitial,
      some (argumentChild argument, childInitial) ∈
        argumentChildren (lowerEnv env.mod env.impl.vars returnTypes) arguments initial →
      ∃ path, SourceLoweringAt ownerRoot (lowerEnv env.mod env.impl.vars returnTypes) ownerInitial path
        (argumentChild argument) childInitial) :
    (rooted : ∃ path, DemandNodeAt siteRoot path anchor) →
    (paths : ∀ argument, argument ∈ arguments →
      ∃ path, DemandNodeAt anchor path (argumentDemandNode argument)) →
    ∀ callee parameters start finish before after sourceRoots,
      tyArgs typingEnv callee parameters arguments start = .ok ((), finish) →
      parameters.length = arguments.length →
      rpArgs env arguments before = .ok (sourceRoots, after) →
      EffectRefinement func after.eff target →
      ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount slots initial upper →
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes) initial func vt upper →
      ReplacementTargetsBound siteTargets initial → GeneratedBuilderState initial →
      NativeRows vt (lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
      SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func
        (lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
      NativeBuilderContinuation func (lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
      ∃ next, ReplayBuilder (lower env.mod) results vt func target
          (lowerEnv env.mod env.impl.vars returnTypes) scopeCount slots
          (lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
        ((lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
          (lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).1.length = arguments.length ∧
          ∀ (index : Nat) (value : ValueId),
            (lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).1[index]? = some value →
            value < (lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2.vals.size ∧
            (∃ roots, sourceRoots[index]? = some roots ∧
              GIR.RootsRefine func (rootsAt next.vals value) roots) ∧
            OperandOccurrence env anchor func next value) ∧
        (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
        OccurrenceLedger env anchor func vt next initial
          (lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 ∧
        CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
          (lowerEnv env.mod env.impl.vars returnTypes)
          (lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 func vt next ∧
        ((lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
          CallArgumentsPhysical env next arguments
            (lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).1) := by
  intro rooted paths callee parameters start finish before after sourceRoots typed shape source wholeEffect ready sites targets generated native metadata continuation
  let le := lowerEnv env.mod env.impl.vars returnTypes
  cases arguments with
  | nil =>
    refine ⟨upper, ready, ?_, fun _ _ => rfl, ?_, sites, ?_⟩
    · simp only [lowerArgs, pure_run, List.length_nil, List.getElem?_nil, reduceCtorEq,
        false_implies, implies_true, and_self]
    · exact EmitsOnly.refl _ _
    · intro live index value syntaxArg row sourceRow
      simp [lowerArgs, pure_run] at row
  | cons argument rest =>
    cases parameters with
    | nil => simp at shape
    | cons parameter parameters =>
      obtain ⟨middleCounter, headTyped, tailTyped⟩ := tyArgs_cons_children typed
      obtain ⟨roots, middleSource, remaining, firstReplay, restReplay, rfl⟩ := rpArgs_cons_contract source
      have firstEffect := effectRefinement_before_of_replay
        (rp_mono_all.2.2.2.2.2.2.2.2.1 env rest)
        (rp_rebinds_mono_all.2.2.2.2.2.2.2.2.1 env rest)
        (rp_flags_mono_all.2.2.2.2.2.2.2.2.1 env rest) restReplay wholeEffect
      obtain ⟨argumentPath, argumentSource⟩ := rows argument initial (by
        simp only [argumentChildren]
        exact List.mem_cons_self)
      obtain ⟨middle, middleReady, firstValue, middleRoots, firstLedger, middleSites, firstPhysical⟩ :=
        step argument (by simp) initial upper rooted (paths argument (by simp))
          ⟨argumentPath, argumentSource⟩ start middleCounter before middleSource roots headTyped firstReplay
          firstEffect ready sites targets generated
          (native.of_prefix (types_lowerArgs rest le (lowerArg argument le initial).2 _ _ rfl))
          (metadata.of_advance (advB_lowerArgs rest le (lowerArg argument le initial).2 _ _ rfl))
          (continuation.of_advance (advB_lowerArgs rest le (lowerArg argument le initial).2 _ _ rfl))
      have restRows : ∀ value childInitial,
          some (argumentChild value, childInitial) ∈ argumentChildren le rest (lowerArg argument le initial).2 →
          ∃ path, SourceLoweringAt ownerRoot le ownerInitial path (argumentChild value) childInitial := by
        intro value childInitial member
        apply rows value childInitial
        change some (argumentChild value, childInitial) ∈
          some (argumentChild argument, initial) :: argumentChildren le rest (lowerArg argument le initial).2
        exact List.mem_cons_of_mem _ member
      obtain ⟨next, nextReady, tailValues, nextRoots, tailLedger, nextSites, tailPhysical⟩ :=
        canonical_typedPhysicalArgumentsOccurrenceFromRows rest (lowerArg argument le initial).2
          (fun child member => step child (by simp [member])) restRows rooted
          (fun child member => paths child (by simp [member])) callee parameters middleCounter finish
          middleSource after remaining tailTyped (by simpa using shape) restReplay wholeEffect
          middleReady middleSites (targets.mono firstLedger.extension)
          (generated.lowerArg argument rfl) native metadata continuation
      let first := lowerArg argument le initial
      let tail := lowerArgs rest le first.2
      have whole : lowerArgs (argument :: rest) le initial = (first.1 :: tail.1, tail.2) := by
        simp only [lowerArgs, bind_run, pure_run]
        rfl
      have valGrowth := (advB_lowerArgs rest le first.2 tail.1 tail.2 rfl).vals
      have ghostGrowth : middle.vals.size ≤ next.vals.size := by
        rw [middleReady.roots.valueSize, nextReady.roots.valueSize]
        exact valGrowth
      have firstFinalLedger := firstLedger.retained ghostGrowth nextRoots
      dsimp only [le] at whole
      rw [whole]
      refine ⟨next, nextReady, ?_, ?_, firstFinalLedger.trans tailLedger, nextSites, ?_⟩
      · intro live
        have firstLive : first.2.cur.isSome = true :=
          (dead_lowerArgs rest).live_before (le := le) (before := first.2)
            (after := tail.2) (result := tail.1) rfl live
        obtain ⟨tailLength, tailValue⟩ := tailValues live
        refine ⟨by simpa using congrArg Nat.succ tailLength, ?_⟩
        intro index value row
        cases index with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at row
          subst value
          obtain ⟨bound, refined, occurrence⟩ := firstValue firstLive
          refine ⟨Nat.lt_of_lt_of_le bound valGrowth, ⟨roots, rfl, ?_⟩,
            occurrence.retained ghostGrowth nextRoots⟩
          rw [nextRoots first.1 (by rw [middleReady.roots.valueSize]; exact bound)]
          exact refined
        | succ index =>
          simp only [List.getElem?_cons_succ] at row
          obtain ⟨bound, ⟨childRoots, sourceRow, refined⟩, occurrence⟩ := tailValue index value row
          exact ⟨bound, ⟨childRoots, sourceRow, refined⟩, occurrence⟩
      · intro index bound
        have growth : upper.vals.size ≤ middle.vals.size := by
          rw [ready.roots.valueSize, middleReady.roots.valueSize]
          exact (advB_lowerArg argument le initial first.1 first.2 rfl).vals
        exact (nextRoots index (Nat.lt_of_lt_of_le bound growth)).trans (middleRoots index bound)
      · intro live index value syntaxArg row sourceRow
        cases index with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at row sourceRow
          subst value syntaxArg
          have firstLive : first.2.cur.isSome = true :=
            (dead_lowerArgs rest).live_before (le := le) (before := first.2)
              (after := tail.2) (result := tail.1) rfl live
          exact (firstPhysical firstLive).retained
            (by rw [middleReady.roots.valueSize]; exact (firstValue firstLive).1) nextRoots
        | succ index =>
          simp only [List.getElem?_cons_succ] at row sourceRow
          exact tailPhysical live index value syntaxArg row sourceRow
termination_by arguments.length

theorem canonical_typedPhysicalArgumentsOccurrence (parent : Expr) (arguments : List Arg)
    (step : ∀ argument, argument ∈ arguments → ∀ initial upper,
      CanonicalPhysicalArgumentOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func
        returnTypes slots target scopeCount siteRoot siteTargets anchor argument initial upper) :
    ∀ initial upper, CanonicalPhysicalArgumentsOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env
      results vt func returnTypes slots target scopeCount siteRoot siteTargets anchor parent arguments initial upper := by
  intro initial upper rooted cursor shape paths callee parameters start finish before after sourceRoots typed arity replay wholeEffect
    ready sites targets generated native metadata continuation
  obtain ⟨parentPath, parentAt⟩ := cursor
  let le := lowerEnv env.mod env.impl.vars returnTypes
  have rows : ∀ argument childInitial,
      some (argumentChild argument, childInitial) ∈ argumentChildren le arguments initial →
      ∃ path, SourceLoweringAt ownerRoot le ownerInitial path (argumentChild argument) childInitial := by
    intro argument childInitial member
    have childMember : some (argumentChild argument, childInitial) ∈
        (Fragment.expression parent).children le initial := by
      rw [shape]
      exact member
    exact (SourceLoweringAt.childrenAt parentAt) (argumentChild argument) childInitial childMember
  exact canonical_typedPhysicalArgumentsOccurrenceFromRows arguments initial
    (fun argument member => step argument member) rows rooted paths callee parameters start finish before after sourceRoots
    typed arity replay wholeEffect ready sites targets generated native metadata continuation

#print axioms canonical_typedPhysicalArgumentsOccurrence

end Goose.Lower.Validation.SourceReplacementWriterLedger
