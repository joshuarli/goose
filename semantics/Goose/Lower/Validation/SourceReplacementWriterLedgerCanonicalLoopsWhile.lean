import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalLoopsBody
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalLoopsSourcePaths
import Goose.Lower.Validation.SummaryPreservationReplayNativeLoopsWhile

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open ReplacementContentFlowSource Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}

open SummaryPreservation.ReplayBuilder


theorem canonical_typedWhileOccurrence {typingEnv output : TEnv} {env : PEnv} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {scope start finish : Nat} {before after : RState}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} {ls : LS} {upper : Prov} (loop : Option LoopCtx)
    (location : ∃ path, DemandNodeAt siteRoot path (.statement (.while condition body origin)))
    (sourceCursor : ∃ path, SourceLoweringAt ownerRoot (lowerEnv env.mod env.impl.vars env.impl.results.toList) ownerInitial path (.statement loop (.while condition body origin)) ls)
    (source : tyStmt typingEnv scope (.while condition body origin) start = .ok (output, finish))
    (replayed : rpStmt env (.while condition body origin) before = .ok ((), after))
    (wholeEffect : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target)
    (scopes : SourceScopesWithin scopeCount (Core.blockScopes none body))
    (stackBounds : typingEnv.inExpr = false → ∀ entered ∈ ls.stack, entered < scopeCount)
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) ls upper)
    (sites : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls (lowerContextAt env.mod env.ctx env.impl) vt upper)
    (targetBounds : ReplacementTargetsBound siteTargets ls)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerStmt loop (.while condition body origin)
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2)
    (projects : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot (lowerContextAt env.mod env.ctx env.impl)
      (lowerStmt loop (.while condition body origin) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2)
    (continuation : NativeBuilderContinuation (lowerContextAt env.mod env.ctx env.impl)
      (lowerStmt loop (.while condition body origin) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2)
    (conditionChild : ∀ targets, CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot targets condition
      (nativeWhileHeader (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls) upper)
    (bodyChild : ∀ targets provenance, CanonicalBlockOccurrenceReplayAt ownerRoot ownerInitial baseline {typingEnv with loops := typingEnv.loops + 1} env results vt target scopeCount siteRoot targets
      (some (nativeWhileContext condition (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls)) [] false body
      (nativeWhileBody condition (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls) provenance) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerStmt loop (.while condition body origin) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 next ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ReturnBoundsPreserved (contextTypedResultUpper env.mod env.ctx) ls upper
        (lowerStmt loop (.while condition body origin) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 next ∧
      OccurrenceLedger env (.statement (.while condition body origin)) (lowerContextAt env.mod env.ctx env.impl) vt next ls
        (lowerStmt loop (.while condition body origin) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 ∧
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerStmt loop (.while condition body origin) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2
        (lowerContextAt env.mod env.ctx env.impl) vt next := by
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let expected := contextTypedResultUpper env.mod env.ctx
  obtain ⟨conditionFinish, bodyType, conditionTyped, bodyTyped, _⟩ := tyStmt_while_children source
  obtain ⟨conditionRoots, conditionState, bodyRoots, bodyRange, conditionReplay, bodyReplay⟩ := native_while_replay replayed
  have conditionEffect := native_loop_source_body_effect bodyReplay wholeEffect
  let allocated := newBlock [] le ls
  have headerEq : allocated.1.1 = ls.blocks.size := by simp [allocated, newBlock0_run]
  have allocatedReady := ready.loopEmptyBlock
  have headerBound : allocated.1.1 < allocated.2.blocks.size := by simp [allocated, newBlock0_run]
  let bridged := Goose.Lower.emitTerm (.br allocated.1.1 []) le allocated.2
  have bridgeReady := allocatedReady.loopBranch allocated.1.1 [] headerBound (by simp) (by simp)
  have bridgeAdv := advB_emitTerm (.br allocated.1.1 []) le allocated.2 bridged.1 bridged.2 rfl
  have headerStill := Nat.lt_of_lt_of_le headerBound bridgeAdv.ext.1
  let started := nativeWhileHeader le ls
  have startedReady := bridgeReady.setCur (some allocated.1.1) (by intro b row; cases row; exact headerStill)
  have allocatedGenerated := generated.newBlock [] (rfl : newBlock [] le ls = allocated)
  have bridgeGenerated := allocatedGenerated.emitTerm (.br allocated.1.1 [])
    (by simpa [Term.successors, allocated, newBlock0_run] using headerBound) (rfl : Goose.Lower.emitTerm (.br allocated.1.1 []) le allocated.2 = bridged)
  have startedGenerated := bridgeGenerated.setCur (some allocated.1.1)
    (by intro b row; cases row; exact headerStill) (rfl : Goose.Lower.setCur (some allocated.1.1) le bridged.2 = ((), started))
  let tested := lowerExpr condition le started
  let bodyAction := fun depth exit => lowerBlock (some ⟨depth, exit, .jump allocated.1.1⟩) [] false body
  have whole : lowerStmt loop (.while condition body origin) le ls =
      lowerWhile allocated.1.1 (lowerExpr condition) bodyAction le started := by
    simp only [lowerStmt, bind_run]
    rfl
  have testedNative : NativeRows vt tested.2 := by
    apply native.of_prefix
    rw [whole]
    change TypePrefix tested.2 (whenLive () _ le tested.2).2
    cases current : tested.2.cur with
    | none => rw [whenLive_none _ _ _ current]; exact .refl _
    | some block =>
      rw [whenLive_some _ _ _ current]
      exact types_loopBody tested.1 (fun _ _ => types_lowerBlock _ _ _ _) (types_emitTerm _) le tested.2 _ _ rfl
  have testedProjects : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot (lowerContextAt env.mod env.ctx env.impl) tested.2 := by
    rw [whole] at projects
    change SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot (lowerContextAt env.mod env.ctx env.impl) (whenLive () _ le tested.2).2 at projects
    cases current : tested.2.cur with
    | none => rw [whenLive_none _ _ _ current] at projects; exact projects
    | some block =>
      rw [whenLive_some _ _ _ current] at projects
      exact projects.of_advance (advB_loopBody tested.1 (fun _ _ => advB_lowerBlock _ _ _ _) (advB_emitTerm _) le tested.2 _ _ rfl)
  have testedContinuation : NativeBuilderContinuation (lowerContextAt env.mod env.ctx env.impl) tested.2 := by
    rw [whole] at continuation
    change NativeBuilderContinuation (lowerContextAt env.mod env.ctx env.impl) (whenLive () _ le tested.2).2 at continuation
    cases current : tested.2.cur with
    | none => rw [whenLive_none _ _ _ current] at continuation; exact continuation
    | some block =>
      rw [whenLive_some _ _ _ current] at continuation
      exact continuation.of_advance (advB_loopBody tested.1 (fun _ _ => advB_lowerBlock _ _ _ _) (advB_emitTerm _) le tested.2 _ _ rfl)
  let headerTargets := allocated.1.1 :: siteTargets
  have headerFresh : ls.blocks.size ≤ allocated.1.1 := by rw [headerEq]; exact Nat.le_refl _
  have startedSites : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot headerTargets le started
      (lowerContextAt env.mod env.ctx env.impl) vt upper :=
    (((sites.reserve allocated.1.1 headerFresh).newBlock []).emitTerm
      (term := .br allocated.1.1 []) (by intro target member; exact Or.inl (List.mem_cons.mpr (Or.inl (by simpa [Term.successors] using member)))) rfl).setCur _
  have startedBounds : ReplacementTargetsBound headerTargets started := by
    intro target member
    rcases List.mem_cons.mp member with rfl | previous
    · exact headerStill
    · exact Nat.lt_of_lt_of_le (targetBounds target previous)
        (Nat.le_trans (advB_newBlock0 le ls _ _ rfl).ext.1 bridgeAdv.ext.1)
  have conditionAt : DemandNodeAt (.statement (.while condition body origin)) [0] (.expression condition) :=
    .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
  have bodyAt : DemandNodeAt (.statement (.while condition body origin)) [1] (.block body) :=
    .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
  have conditionSource : ∃ path, DemandNodeAt siteRoot path (.expression condition) := by
    obtain ⟨path, parent⟩ := location
    exact ⟨path ++ [0], sourcePath_append parent conditionAt⟩
  have bodySource : ∃ path, DemandNodeAt siteRoot path (.block body) := by
    obtain ⟨path, parent⟩ := location
    exact ⟨path ++ [1], sourcePath_append parent bodyAt⟩
  obtain ⟨conditionProv, conditionReady, conditionValue, conditionGrowth, conditionLedger, conditionSites⟩ := conditionChild headerTargets conditionSource (by
      obtain ⟨path, located⟩ := sourceCursor
      exact ⟨path ++ [0], located.child rfl⟩) .bool start conditionFinish
    before conditionState conditionRoots conditionTyped conditionReplay conditionEffect startedReady startedSites startedBounds startedGenerated testedNative testedProjects testedContinuation
  have testedGenerated := startedGenerated.lowerExpr condition (rfl : lowerExpr condition le started = tested)
  have testedAdv := advB_lowerExpr condition le started tested.1 tested.2 rfl
  have startValues : started.vals = ls.vals := by
    change bridged.2.vals = ls.vals
    cases active : allocated.2.cur with
    | none => simp [bridged, emitTerm_none _ _ active, allocated, newBlock0_run]
    | some b => simp [bridged, emitTerm_run _ _ active, allocated, newBlock0_run]
  have startStack : started.stack = ls.stack := by
    change bridged.2.stack = ls.stack
    exact bridgeAdv.stack.trans (advB_newBlock0 le ls allocated.1 allocated.2 rfl).stack
  have entryReturns : ReturnMembershipFrame ls started := by
    apply ReturnFrameRun.of_absence (fun _ => ReturnFrames.returnAbsent_header0 (fun _ => ReturnFrames.returnAbsent_pure ()))
      le ls () started
    simp only [bind_run, pure_run]
    rfl
  have entryTransfer : ReturnBoundsPreserved expected ls upper started upper :=
    .frame ready.symbols ready.roots.valueSize (fun _ _ => rfl) entryReturns
  have conditionTransfer : ReturnBoundsPreserved expected started upper tested.2 conditionProv :=
    .frame startedReady.symbols startedReady.roots.valueSize conditionGrowth
      (source_expression_return_frame conditionTyped le started tested.1 tested.2 rfl)
  cases current : tested.2.cur with
  | none =>
    have stopped : lowerStmt loop (.while condition body origin) le ls = ((), tested.2) := by
      rw [whole]
      change whenLive () _ le tested.2 = ((), tested.2)
      exact whenLive_none _ _ _ current
    refine ⟨conditionProv, by rw [stopped]; exact conditionReady, conditionGrowth,
      by rw [stopped]; exact entryTransfer.trans conditionTransfer, ?_, ?_⟩
    · rw [stopped]
      have entryLedger : OccurrenceLedger env (.statement (.while condition body origin))
          (lowerContextAt env.mod env.ctx env.impl) vt conditionProv ls started :=
        (emitsOnly_newBlock _ [] le ls _ _ rfl).trans
          ((emitsOnly_emitTerm _ (occurrenceInstructionTerm _) le allocated.2 _ _ rfl).trans (.of_blocks rfl))
      exact entryLedger.trans (conditionLedger.underRoot conditionAt)
    · rw [stopped]
      exact conditionSites.weaken (by intro target member; exact List.mem_cons_of_mem _ member)
  | some block =>
    have live : tested.2.cur.isSome = true := by simp [current]
    have nativeLoop : NativeRows vt (Goose.Lower.loopBody tested.1 bodyAction (Goose.Lower.emitTerm (.br allocated.1.1 [])) le tested.2).2 := by
      rw [whole] at native
      change NativeRows vt (whenLive () _ le tested.2).2 at native
      rw [whenLive_some _ _ _ current] at native
      exact native
    have loopProjects := projects
    rw [whole] at loopProjects
    change SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot (lowerContextAt env.mod env.ctx env.impl) (whenLive () _ le tested.2).2 at loopProjects
    rw [whenLive_some _ _ _ current] at loopProjects
    have loopContinuation := continuation
    rw [whole] at loopContinuation
    change NativeBuilderContinuation (lowerContextAt env.mod env.ctx env.impl) (whenLive () _ le tested.2).2 at loopContinuation
    rw [whenLive_some _ _ _ current] at loopContinuation
    have backReturns : ReturnFrameRun (Goose.Lower.emitTerm (.br allocated.1.1 [])) :=
      .of_absence (fun _ => ReturnFrames.returnAbsent_emitTerm _ (by intro _ _ same; cases same))
    obtain ⟨next, nextReady, growth, transfer, loopLedger, loopSites⟩ := canonical_loopBodyOccurrence
      (root := .statement (.while condition body origin)) conditionReady conditionSites
      (startedBounds.mono testedAdv.ext) expected tested.1
      (conditionValue live).bound live bodyAction (Goose.Lower.emitTerm (.br allocated.1.1 [])) testedGenerated nativeLoop loopProjects loopContinuation
      (fun _ _ => advB_lowerBlock _ _ _ _) (advB_emitTerm _) (types_emitTerm _) backReturns
      (by
        dsimp only
        intro stateReady stateSites stateBounds stateGenerated stateNative exitBound blocks values bodyProjects bodyContinuation
        have header : allocated.1.1 < (loopBodyEntry tested.1 le tested.2).blocks.size :=
          Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le headerStill testedAdv.ext.1) blocks
        have bounds : LoopBuilderTargets (some ⟨tested.2.stack.length, (fork tested.1 le tested.2).1.2, .jump allocated.1.1⟩)
            (loopBodyEntry tested.1 le tested.2) := ⟨exitBound, header⟩
        have replayBounds : LoopReplayBounds (some ⟨tested.2.stack.length, (fork tested.1 le tested.2).1.2, .jump allocated.1.1⟩)
            scopeCount (loopBodyEntry tested.1 le tested.2) := by
          constructor
          · trivial
          · rw [native_loopBody_entry_stack]
            simp
        obtain ⟨next, nextReady, _, retained, transfer, bodyLedger, bodySites⟩ := bodyChild
          ((fork tested.1 le tested.2).1.2 :: headerTargets) conditionProv bodySource (by
            obtain ⟨path, located⟩ := sourceCursor
            refine ⟨path ++ [1], located.child ?_⟩
            exact canonical_while_body_child le ls loop condition body origin live) bodyType conditionFinish finish
          conditionState after bodyRoots bodyRange bodyTyped bodyReplay wholeEffect scopes (by simp) (by simp) (by simp)
          (by
            intro plain entered member
            apply stackBounds plain entered
            change entered ∈ (nativeWhileBody condition le ls).stack at member
            change entered ∈ (loopBodyEntry tested.1 le tested.2).stack at member
            rw [native_loopBody_entry_stack, testedAdv.stack, startStack] at member
            exact member)
          stateReady stateSites stateBounds stateGenerated (by simpa only [nativeWhileContext, nativeWhileBody, headerEq] using bounds)
          (by simpa only [nativeWhileContext, nativeWhileBody, headerEq] using replayBounds)
          (by simp [OccurrenceLoopCounterTyped, nativeWhileContext])
          (by
            intro target member
            change target ∈ [(fork tested.1 le tested.2).1.2, allocated.1.1] at member
            rcases List.mem_cons.mp member with first | rest
            · exact List.mem_cons.mpr (Or.inl first)
            · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp rest))))
          stateNative bodyProjects bodyContinuation
        exact ⟨next, nextReady, retained, transfer, bodyLedger.underRoot bodyAt, bodySites⟩)
      (by
        intro state provenance stateReady stateSites blocks values priorRoots
        exact ⟨provenance, stateReady.loopBranch allocated.1.1 []
          (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le headerStill testedAdv.ext.1) blocks) (by simp) (by simp),
          (fun _ _ => rfl), emitsOnly_emitTerm _ (occurrenceInstructionTerm _) _ _ _ _ rfl,
          stateSites.emitTerm (by intro target member; exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl (by simpa [Term.successors] using member))))) rfl⟩)
    have same : lowerStmt loop (.while condition body origin) le ls =
        Goose.Lower.loopBody tested.1 bodyAction (Goose.Lower.emitTerm (.br allocated.1.1 [])) le tested.2 := by
      rw [whole]
      change whenLive () _ le tested.2 = _
      rw [whenLive_some _ _ _ current]
    refine ⟨next, by rw [same]; exact nextReady, ?_, ?_, ?_, ?_⟩
    · intro old bound
      have conditionBound : old < conditionProv.vals.size := by
        rw [conditionReady.roots.valueSize]
        apply Nat.lt_of_lt_of_le _ testedAdv.vals
        rw [startValues]
        simpa only [ready.roots.valueSize] using bound
      rw [growth old conditionBound, conditionGrowth old bound]
    · rw [same]
      exact entryTransfer.trans (conditionTransfer.trans transfer)
    · rw [same]
      have entryLedger : OccurrenceLedger env (.statement (.while condition body origin))
          (lowerContextAt env.mod env.ctx env.impl) vt next ls started :=
        (emitsOnly_newBlock _ [] le ls _ _ rfl).trans
          ((emitsOnly_emitTerm _ (occurrenceInstructionTerm _) le allocated.2 _ _ rfl).trans (.of_blocks rfl))
      have nextGrowth : conditionProv.vals.size ≤ next.vals.size := by
        rw [conditionReady.roots.valueSize, nextReady.roots.valueSize]
        exact (advB_loopBody tested.1 (fun _ _ => advB_lowerBlock _ _ _ _) (advB_emitTerm _) le tested.2 _ _ rfl).vals
      exact (entryLedger.trans ((conditionLedger.underRoot conditionAt).retained nextGrowth growth)).trans loopLedger
    · rw [same]
      exact loopSites.weaken (by intro target member; exact List.mem_cons_of_mem _ member)



theorem canonical_statementOccurrence_while {typingEnv : TEnv} {env : PEnv}
    {condition : Expr} {body : Core.Block} {origin : OriginId}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId}
    {loop : Option LoopCtx} {scope : ScopeId} {initial : LS} {upper : Prov}
    (conditionChild : ∀ targets, CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot targets condition
      (nativeWhileHeader (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial) upper)
    (bodyChild : ∀ targets provenance, CanonicalBlockOccurrenceReplayAt ownerRoot ownerInitial baseline {typingEnv with loops := typingEnv.loops + 1}
      env results vt target scopeCount siteRoot targets
      (some (nativeWhileContext condition (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial)) [] false body
      (nativeWhileBody condition (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial) provenance) :
    CanonicalStatementOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets loop scope
      (.while condition body origin) initial upper := by
  intro location sourceCursor output start finish before after typed replay ceiling scopes stack ready sites targetBounds
    generated loopTargets loopReplay counterTyped included native projects continuation
  have bodyScopes : SourceScopesWithin scopeCount (Core.blockScopes none body) := by
    apply scopes.of_subset
    intro entry member
    exact List.mem_append_right _ member
  exact canonical_typedWhileOccurrence loop location sourceCursor typed replay ceiling bodyScopes stack ready sites targetBounds
    generated native projects continuation conditionChild bodyChild

#print axioms canonical_statementOccurrence_while

end Goose.Lower.Validation.SourceReplacementWriterLedger
