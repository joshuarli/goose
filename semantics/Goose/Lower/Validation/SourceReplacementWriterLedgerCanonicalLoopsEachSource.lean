import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.ExpressionTypingGenerated
import Goose.Lower.Validation.SourceRootShapeReads
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeFrames
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlSteps
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessKernel
import Goose.Lower.Validation.SummaryPreservationReplayTypedViews
import Goose.Lower.Validation.SummaryPreservationReplayLoopsEachSource

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open ReplacementContentFlowSource Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}



theorem canonical_typedEachSourceOccurrence {typingEnv : TEnv} {env : PEnv} {view : View} {element : Ty} {writable : Bool}
    {start finish : Nat} {before after : RState} {sourceRoots : List RootRef}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} {ls : LS} {upper : Prov}
    (tables : SourceRootTables typingEnv env)
    (location : ∃ path, DemandNodeAt siteRoot path (.view view))
    (sourceCursor : ∃ path, SourceLoweringAt ownerRoot (lowerEnv env.mod env.impl.vars env.impl.results.toList) ownerInitial path (.view view) ls)
    (typing : tyView typingEnv view start = .ok ((element, writable), finish))
    (source : rpView env view before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target)
    (closed : ParameterRootsClosed (lowerContextAt env.mod env.ctx env.impl))
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) ls upper)
    (sites : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls (lowerContextAt env.mod env.ctx env.impl) vt upper)
    (targetBounds : ReplacementTargetsBound siteTargets ls)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerEachSource view (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2)
    (projects : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot (lowerContextAt env.mod env.ctx env.impl)
      (lowerEachSource view (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2)
    (continuation : NativeBuilderContinuation (lowerContextAt env.mod env.ctx env.impl)
      (lowerEachSource view (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2)
    (placeChild : ∀ place, view = .of place → CanonicalPlaceOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets place ls upper)
    (expressionChild : ∀ expression, view = .val expression → CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets expression ls upper) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerEachSource view (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 next ∧
      ((lowerEachSource view (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
        ReplayEachSource (lowerContextAt env.mod env.ctx env.impl) next
          (lowerEachSource view (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2
          (lowerEachSource view (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 sourceRoots element) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env (.view view) (lowerContextAt env.mod env.ctx env.impl) vt next ls
        (lowerEachSource view (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 ∧
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerEachSource view (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2
        (lowerContextAt env.mod env.ctx env.impl) vt next := by
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  have nativeView : NativeRows vt (lowerView view le ls).2 := by cases view <;> exact native
  have viewProjects : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot (lowerContextAt env.mod env.ctx env.impl)
      (lowerView view le ls).2 := by cases view <;> exact projects
  have viewContinuation : NativeBuilderContinuation (lowerContextAt env.mod env.ctx env.impl)
      (lowerView view le ls).2 := by cases view <;> exact continuation
  cases view with
  | of place =>
    have viewReplay := source
    simp only [Core.tyView] at typing
    obtain ⟨info, next, placeTyped, _⟩ := (st_bind_ok _ _ _ _).mp typing
    simp only [rpView] at source
    obtain ⟨placeRoots, placeState, placeReplay, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, readState, readReplay, source⟩ := (st_bind_ok _ _ _ _).mp source
    have pair := (st_pure_ok _ _ _).mp source
    cases pair
    let placeResult := lowerPlace place le ls
    have placeEffect := effectRefinement_before_of_replay (PMono.addReads sourceRoots)
      (PMonoRebinds.addReads sourceRoots) (PFlagsMono.addReads sourceRoots) readReplay wholeEffect
    let mode : SnapshotMode := match place with | .var _ | .global _ => .owner | _ => .borrowed
    have viewWhole : lowerView (.of place) le ls = Goose.Lower.emitDef
        (.snapshot mode placeResult.1) le placeResult.2 := by
      simp only [lowerView, bind_run]
      cases place <;> rfl
    have childNative : NativeRows vt placeResult.2 := by
      apply nativeView.of_prefix
      rw [viewWhole]
      exact types_emitDef _ le placeResult.2 _ _ rfl
    have childProjects := viewProjects
    rw [viewWhole] at childProjects
    have placeProjects := childProjects.of_advance (advB_emitDef
      (.snapshot mode placeResult.1) le placeResult.2 _ _ rfl)
    have finalContinuation := viewContinuation
    rw [viewWhole] at finalContinuation
    have placeContinuation := finalContinuation.of_advance (advB_emitDef
      (.snapshot mode placeResult.1) le placeResult.2 _ _ rfl)
    obtain ⟨placeProv, placeReady, placeValue, placeGrowth, placeLedger, placeSites⟩ :=
      placeChild place rfl (accessChildPresent location 0 rfl) (by
        obtain ⟨path, located⟩ := sourceCursor
        exact ⟨path ++ [0], located.child rfl⟩) info start next before placeState sourceRoots placeTyped placeReplay placeEffect ready sites targetBounds generated childNative placeProjects placeContinuation
    obtain ⟨viewProv, viewReady, viewValue, viewGrowth⟩ := placeReady.placeView .readOnly element closed
      placeReplay viewReplay wholeEffect (show lowerPlace place le ls = (placeResult.1, placeResult.2) from rfl) placeValue
    let sampled := Goose.Lower.emitDef (.snapshot mode placeResult.1) le placeResult.2
    have whole : lowerEachSource (.of place) le ls = ((some placeResult.1, sampled.1), sampled.2) := by
      simp only [lowerEachSource, bind_run, pure_run]
      cases place <;> rfl
    have sameView : lowerView (.of place) le ls = sampled := by
      simp only [lowerView, bind_run]
      cases place <;> rfl
    rw [sameView] at viewReady viewValue
    refine ⟨viewProv, ?_, ?_, ?_, ?_, ?_⟩
    · rw [whole]
      exact viewReady
    · rw [whole]
      intro live
      refine ⟨viewValue live, ?_⟩
      intro address same
      cases same
      have placeLive := (dead_emitDef (.snapshot mode placeResult.1)).live_before
        (show Goose.Lower.emitDef (.snapshot mode placeResult.1) le placeResult.2 = (sampled.1, sampled.2) from rfl) live
      obtain ⟨bound, refined⟩ := placeValue placeLive
      have beforeBound : placeResult.1 < placeProv.vals.size := by simpa only [placeReady.roots.valueSize] using bound
      refine ⟨Nat.lt_of_lt_of_le bound (advB_emitDef (.snapshot mode placeResult.1) le placeResult.2 sampled.1 sampled.2 rfl).vals, ?_⟩
      rw [viewGrowth placeResult.1 beforeBound]
      exact refined
    · intro index bound
      have placeBound : index < placeProv.vals.size := by
        rw [placeReady.roots.valueSize]
        exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound)
          (advB_lowerPlace place le ls placeResult.1 placeResult.2 rfl).vals
      rw [viewGrowth index placeBound, placeGrowth index bound]
    · rw [whole]
      have growth := accessRootsGrowth placeReady viewReady (advB_emitDef (.snapshot mode placeResult.1) le placeResult.2 _ _ rfl).vals
      have suffix : OccurrenceLedger env (.view (.of place)) (lowerContextAt env.mod env.ctx env.impl) vt viewProv placeResult.2 sampled.2 := by
        apply accessEmitDefinition rfl
        intro live
        refine ⟨?_, ?_, ?_, InstructionOccurrences.no_store (by intros; intro same; cases same), ?_⟩
        · intro operand member reference
          have same : operand = placeResult.1 := by simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] using member
          subst operand
          have oldBound : placeResult.1 < placeProv.vals.size := by
            rw [placeReady.roots.valueSize]
            exact (placeValue live).1
          apply accessOperandPlace (accessChildNode 0 rfl) placeReplay (Nat.lt_of_lt_of_le oldBound growth)
          rw [viewGrowth placeResult.1 oldBound]
          exact (placeValue live).2
        · intro value address same; cases same
        · intro value callee args origin same; cases same
        · intro operand member mutability payload row
          have same : operand = placeResult.1 := by simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] using member
          subst operand
          have oldBound : placeResult.1 < placeProv.vals.size := by
            rw [placeReady.roots.valueSize]
            exact (placeValue live).1
          refine .place placeResult.1 env [0] place before sourceRoots placeState rfl
            (accessChildNode 0 rfl) placeReplay (Nat.lt_of_lt_of_le oldBound growth) ?_
          rw [viewGrowth placeResult.1 oldBound]
          exact (placeValue live).2
      exact ((placeLedger.retained growth viewGrowth).underRoot (accessChildNode 0 rfl)).trans suffix
    · rw [whole]
      exact placeSites.emitDef rfl (accessRootsGrowth placeReady viewReady (advB_emitDef (.snapshot mode placeResult.1) le placeResult.2 _ _ rfl).vals) viewGrowth
  | val expression =>
    simp only [Core.tyView] at typing
    obtain ⟨type, next, expressionTyped, viewTyped⟩ := (st_bind_ok _ _ _ _).mp typing
    let expressionResult := lowerExpr expression le ls
    have childNative : NativeRows vt expressionResult.2 := by
      apply nativeView.of_prefix
      exact types_emitDef (.sliceView expressionResult.1) le expressionResult.2 _ _ rfl
    have expressionProjects := viewProjects.of_advance
      (advB_emitDef (.sliceView expressionResult.1) le expressionResult.2 _ _ rfl)
    have expressionContinuation := viewContinuation.of_advance
      (advB_emitDef (.sliceView expressionResult.1) le expressionResult.2 _ _ rfl)
    obtain ⟨expressionProv, expressionReady, typedValue, expressionGrowth, expressionLedger, expressionSites⟩ :=
      expressionChild expression rfl (accessChildPresent location 0 rfl) (by
        obtain ⟨path, located⟩ := sourceCursor
        exact ⟨path ++ [0], located.child rfl⟩) type start next before after sourceRoots expressionTyped source wholeEffect ready sites targetBounds generated childNative expressionProjects expressionContinuation
    have expressionValue := fun live => And.intro (typedValue live).bound (typedValue live).refined
    obtain ⟨viewProv, viewReady, viewValue, viewGrowth⟩ := expressionReady.valueView .readOnly element
      source source (show lowerExpr expression le ls = (expressionResult.1, expressionResult.2) from rfl) expressionValue
    let sampled := Goose.Lower.emitDef (.sliceView expressionResult.1) le expressionResult.2
    have whole : lowerEachSource (.val expression) le ls = ((none, sampled.1), sampled.2) := by
      simp only [lowerEachSource, bind_run, pure_run]
      rfl
    have sameView : lowerView (.val expression) le ls = sampled := by
      simp only [lowerView, bind_run]
      rfl
    rw [sameView] at viewReady viewValue
    refine ⟨viewProv, ?_, ?_, ?_, ?_, ?_⟩
    · rw [whole]
      exact viewReady
    · rw [whole]
      intro live
      exact ⟨viewValue live, by intro address impossible; cases impossible⟩
    · intro index bound
      have expressionBound : index < expressionProv.vals.size := by
        rw [expressionReady.roots.valueSize]
        exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound)
          (advB_lowerExpr expression le ls expressionResult.1 expressionResult.2 rfl).vals
      rw [viewGrowth index expressionBound, expressionGrowth index bound]
    · rw [whole]
      have growth := accessRootsGrowth expressionReady viewReady (advB_emitDef (.sliceView expressionResult.1) le expressionResult.2 _ _ rfl).vals
      have suffix : OccurrenceLedger env (.view (.val expression)) (lowerContextAt env.mod env.ctx env.impl) vt viewProv expressionResult.2 sampled.2 := by
        apply accessEmitDefinition rfl
        intro live
        refine ⟨?_, ?_, ?_, InstructionOccurrences.no_store (by intros; intro same; cases same), ?_⟩
        · intro operand member reference
          have same : operand = expressionResult.1 := by simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] using member
          subst operand
          have oldBound : expressionResult.1 < expressionProv.vals.size := by
            rw [expressionReady.roots.valueSize]
            exact (typedValue live).bound
          apply accessOperandExpression (accessChildNode 0 rfl) source (Nat.lt_of_lt_of_le oldBound growth)
          rw [viewGrowth expressionResult.1 oldBound]
          exact (typedValue live).refined
        · intro value address same; cases same
        · intro value callee args origin same; cases same
        · intro operand member mutability payload row
          have same : operand = expressionResult.1 := by simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] using member
          subst operand
          have sourceRun : lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars env.impl.results.toList) ls = expressionResult := by
            rw [← tables.moduleEq, ← tables.variablesEq]
          have typed := lowerExpr_generated_typed expression expressionTyped sourceRun live generated
          have recorded := childNative expressionResult.1 (.data type) typed
          simp only [recorded, Option.some.injEq, VTy.data.injEq] at row
          rw [row] at viewTyped
          exact (rej_ok _ _ _ _).mp viewTyped |>.elim
      exact ((expressionLedger.retained growth viewGrowth).underRoot (accessChildNode 0 rfl)).trans suffix
    · rw [whole]
      exact expressionSites.emitDef rfl (accessRootsGrowth expressionReady viewReady (advB_emitDef (.sliceView expressionResult.1) le expressionResult.2 _ _ rfl).vals) viewGrowth

#print axioms canonical_typedEachSourceOccurrence

end Goose.Lower.Validation.SourceReplacementWriterLedger
