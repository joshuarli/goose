import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalLoopsRangeAction
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalLoopsSourcePaths
import Goose.Lower.Validation.SummaryPreservationReplayNativeLoopsRange

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open ReplacementContentFlowSource Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}

open SummaryPreservation.ReplayBuilder


theorem canonical_typedRangeOccurrence {typingEnv output : TEnv} {env : PEnv} {variableId : VarId} {low high : Expr}
    {body : Core.Block} {origin : OriginId} {scope start finish : Nat} {before after : RState}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} {ls : LS} {upper : Prov} (loop : Option LoopCtx)
    (tables : SourceRootTables typingEnv env)
    (location : ∃ path, DemandNodeAt siteRoot path (.statement (.forRange variableId low high body origin)))
    (sourceCursor : ∃ path, SourceLoweringAt ownerRoot (lowerEnv env.mod env.impl.vars env.impl.results.toList) ownerInitial path (.statement loop (.forRange variableId low high body origin)) ls)
    (source : tyStmt typingEnv scope (.forRange variableId low high body origin) start = .ok (output, finish))
    (replayed : rpStmt env (.forRange variableId low high body origin) before = .ok ((), after))
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
    (native : NativeRows vt (lowerStmt loop (.forRange variableId low high body origin)
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2)
    (projects : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot
      (lowerContextAt env.mod env.ctx env.impl)
      (lowerStmt loop (.forRange variableId low high body origin)
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2)
    (continuation : NativeBuilderContinuation (lowerContextAt env.mod env.ctx env.impl)
      (lowerStmt loop (.forRange variableId low high body origin)
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2)
    (lowChild : CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets low ls upper)
    (highChild : ∀ provenance, CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets high
      (lowerExpr low (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 provenance)
    (bodyChild : ∀ targets depth header exit type counter state provenance,
      let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
      let first := lowerExpr low le ls
      let last := lowerExpr high le first.2
      type = (intTyOf first.1 le last.2).1 → header = last.2.blocks.size → counter = last.2.vals.size →
      state = nativeRangeBody type counter last.1 le (nativeRangeStart low high le ls) →
      CanonicalBlockOccurrenceReplayAt ownerRoot ownerInitial baseline {typingEnv with loops := typingEnv.loops + 1, visible := variableId :: typingEnv.visible}
        env results vt target scopeCount siteRoot targets (some ⟨depth, exit, .next header type counter⟩)
        [(variableId, counter, origin)] false body state provenance) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerStmt loop (.forRange variableId low high body origin) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 next ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ReturnBoundsPreserved (contextTypedResultUpper env.mod env.ctx) ls upper
        (lowerStmt loop (.forRange variableId low high body origin) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 next ∧
      OccurrenceLedger env (.statement (.forRange variableId low high body origin)) (lowerContextAt env.mod env.ctx env.impl) vt next ls
        (lowerStmt loop (.forRange variableId low high body origin) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 ∧
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerStmt loop (.forRange variableId low high body origin) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2
        (lowerContextAt env.mod env.ctx env.impl) vt next := by
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let expected := contextTypedResultUpper env.mod env.ctx
  obtain ⟨localVar, integer, lowStart, lowFinish, highFinish, bodyType, declaration, lowTyped, highTyped, localType, bodyTyped, _⟩ :=
    tyStmt_forRange_children source
  obtain ⟨sourceStart, lowRoots, lowState, highRoots, highState, bodyRoots, bodyRange, lowReplay, highReplay, bodyReplay⟩ :=
    native_range_replay replayed
  have highEffect := native_loop_source_body_effect bodyReplay wholeEffect
  have lowEffect := effectRefinement_before_expression highReplay highEffect
  let first := lowerExpr low le ls
  let last := lowerExpr high le first.2
  have lastNative : NativeRows vt last.2 := by
    apply native.of_prefix
    change TypePrefix last.2 (whenLive () _ le last.2).2
    cases current : last.2.cur with
    | none => rw [whenLive_none _ _ _ current]; exact .refl _
    | some block =>
      rw [whenLive_some _ _ _ current]
      let tail : B Unit := do
        let type ← intTyOf first.1
        let (header, parameters) ← newBlock [.data (.int type)]
        let counter := parameters.headD 0
        Goose.Lower.emitTerm (.br header [first.1])
        Goose.Lower.setCur (some header)
        lowerRange type counter last.1 header (fun depth exit => lowerBlock
          (some ⟨depth, exit, .next header type counter⟩) [(variableId, counter, origin)] false body)
      have typed : TypeRun tail := by
        apply TypeRun.bind (types_intTyOf first.1)
        intro type
        apply TypeRun.bind (types_newBlock [.data (.int type)])
        intro pair
        rcases pair with ⟨header, parameters⟩
        exact TypeRun.bind (types_emitTerm _) (fun _ => TypeRun.bind (types_setCur _)
          (fun _ => types_lowerRange _ _ _ _ (fun _ _ => types_lowerBlock _ _ _ _)))
      exact typed le last.2 (tail le last.2).1 (tail le last.2).2 rfl
  have lastProjects : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot
      (lowerContextAt env.mod env.ctx env.impl) last.2 := by
    apply projects.of_advance
    change last.2.Adv (whenLive () _ le last.2).2
    apply advB_whenLive () (fun _ => ?_) le last.2 _ _ rfl
    apply AdvB.bind (advB_intTyOf first.1)
    intro type
    exact advB_header1 (.data (.int type)) first.1
      (tail := fun header counter => lowerRange type counter last.1 header
        (fun depth exit => lowerBlock (some ⟨depth, exit, .next header type counter⟩)
          [(variableId, counter, origin)] false body))
      (fun _ _ => advB_lowerRange _ _ _ _ (fun _ _ => advB_lowerBlock _ _ _ _))
  have firstProjects := lastProjects.of_advance (advB_lowerExpr high le first.2 last.1 last.2 rfl)
  have lastContinuation : NativeBuilderContinuation
      (lowerContextAt env.mod env.ctx env.impl) last.2 := by
    apply continuation.of_advance
    change last.2.Adv (whenLive () _ le last.2).2
    apply advB_whenLive () (fun _ => ?_) le last.2 _ _ rfl
    apply AdvB.bind (advB_intTyOf first.1)
    intro type
    exact advB_header1 (.data (.int type)) first.1
      (tail := fun header counter => lowerRange type counter last.1 header
        (fun depth exit => lowerBlock (some ⟨depth, exit, .next header type counter⟩)
          [(variableId, counter, origin)] false body))
      (fun _ _ => advB_lowerRange _ _ _ _ (fun _ _ => advB_lowerBlock _ _ _ _))
  have firstContinuation := lastContinuation.of_advance (advB_lowerExpr high le first.2 last.1 last.2 rfl)
  have firstNative := lastNative.of_prefix (types_lowerExpr high le first.2 last.1 last.2 rfl)
  have lowAt : DemandNodeAt (.statement (.forRange variableId low high body origin)) [0] (.expression low) :=
    .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
  have highAt : DemandNodeAt (.statement (.forRange variableId low high body origin)) [1] (.expression high) :=
    .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
  have bodyAt : DemandNodeAt (.statement (.forRange variableId low high body origin)) [2] (.block body) :=
    .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
  have lowSource : ∃ path, DemandNodeAt siteRoot path (.expression low) := by
    obtain ⟨path, parent⟩ := location
    exact ⟨path ++ [0], sourcePath_append parent lowAt⟩
  have highSource : ∃ path, DemandNodeAt siteRoot path (.expression high) := by
    obtain ⟨path, parent⟩ := location
    exact ⟨path ++ [1], sourcePath_append parent highAt⟩
  have bodySource : ∃ path, DemandNodeAt siteRoot path (.block body) := by
    obtain ⟨path, parent⟩ := location
    exact ⟨path ++ [2], sourcePath_append parent bodyAt⟩
  obtain ⟨firstProv, firstReady, firstValue, firstGrowth, firstLedger, firstSites⟩ := lowChild lowSource (by
    obtain ⟨path, located⟩ := sourceCursor
    exact ⟨path ++ [0], located.child rfl⟩) (.int integer) lowStart lowFinish
    sourceStart lowState lowRoots lowTyped lowReplay lowEffect ready sites targetBounds generated firstNative firstProjects firstContinuation
  have firstGenerated := generated.lowerExpr low (rfl : lowerExpr low le ls = first)
  obtain ⟨lastProv, lastReady, lastValue, lastGrowth, lastLedger, lastSites⟩ := highChild firstProv highSource (by
    obtain ⟨path, located⟩ := sourceCursor
    exact ⟨path ++ [1], located.child rfl⟩) (.int integer) lowFinish highFinish
    lowState highState highRoots highTyped highReplay highEffect firstReady firstSites (targetBounds.mono (advB_lowerExpr low le ls _ _ rfl).ext) firstGenerated lastNative lastProjects lastContinuation
  have lastGenerated := firstGenerated.lowerExpr high (rfl : lowerExpr high le first.2 = last)
  have firstAdv := advB_lowerExpr low le ls first.1 first.2 rfl
  have lastAdv := advB_lowerExpr high le first.2 last.1 last.2 rfl
  have firstTransfer : ReturnBoundsPreserved expected ls upper first.2 firstProv :=
    .frame ready.symbols ready.roots.valueSize firstGrowth (source_expression_return_frame lowTyped le ls first.1 first.2 rfl)
  have lastTransfer : ReturnBoundsPreserved expected first.2 firstProv last.2 lastProv :=
    .frame firstReady.symbols firstReady.roots.valueSize lastGrowth (source_expression_return_frame highTyped le first.2 last.1 last.2 rfl)
  have firstSize : upper.vals.size ≤ firstProv.vals.size := by rw [ready.roots.valueSize, firstReady.roots.valueSize]; exact firstAdv.vals
  have oldGrowth : ∀ old, old < upper.vals.size → rootsAt lastProv.vals old = rootsAt upper.vals old := by
    intro old bound
    rw [lastGrowth old (Nat.lt_of_lt_of_le bound firstSize), firstGrowth old bound]
  have lastGhostGrowth : firstProv.vals.size ≤ lastProv.vals.size := by
    rw [firstReady.roots.valueSize, lastReady.roots.valueSize]
    exact lastAdv.vals
  have expressionsLedger : OccurrenceLedger env (.statement (.forRange variableId low high body origin))
      (lowerContextAt env.mod env.ctx env.impl) vt lastProv ls last.2 :=
    ((firstLedger.underRoot lowAt).retained lastGhostGrowth lastGrowth).trans (lastLedger.underRoot highAt)
  cases current : last.2.cur with
  | none =>
    have stopped : lowerStmt loop (.forRange variableId low high body origin) le ls = ((), last.2) := by
      simp only [lowerStmt, bind_run]
      exact whenLive_none _ _ _ current
    exact ⟨lastProv, by rw [stopped]; exact lastReady, oldGrowth, by rw [stopped]; exact firstTransfer.trans lastTransfer,
      by rw [stopped]; exact expressionsLedger, by rw [stopped]; exact lastSites⟩
  | some block =>
    have live : last.2.cur.isSome = true := by simp [current]
    have firstLive := (dead_lowerExpr high).live_before (rfl : lowerExpr high le first.2 = last) live
    have firstResult := firstValue firstLive
    have lastResult := lastValue live
    have firstBound := Nat.lt_of_lt_of_le firstResult.bound lastAdv.vals
    have firstOld : first.1 < firstProv.vals.size := by simpa only [firstReady.roots.valueSize] using firstResult.bound
    have firstScalar : rootsAt lastProv.vals first.1 = [] := (lastGrowth first.1 firstOld).trans (firstResult.scalar rfl)
    cases typeRun : intTyOf first.1 le last.2 with
    | mk actualType typeState =>
      have stateEq := intTyOf_eq typeRun
      subst typeState
      let allocated := newBlock [.data (.int actualType)] le last.2
      let counter := allocated.1.2.headD 0
      have counterEq : counter = last.2.vals.size := by simp [counter, allocated, newBlock1_run]
      have headerEq : allocated.1.1 = last.2.blocks.size := by simp [allocated, newBlock1_run]
      have headerBound : allocated.1.1 < allocated.2.blocks.size := by simp [allocated, newBlock1_run]
      have counterBound : counter < allocated.2.vals.size := by simp [counterEq, allocated, newBlock1_run]
      obtain ⟨headerProv, headerReady, counterEmpty, headerGrowth⟩ := lastReady.loopScalarBlock (.data (.int actualType))
      have firstAfterHeader : rootsAt headerProv.vals first.1 = [] :=
        (headerGrowth first.1 (by simpa only [lastReady.roots.valueSize] using firstBound)).trans firstScalar
      let bridged := Goose.Lower.emitTerm (.br allocated.1.1 [first.1]) le allocated.2
      have bridgeReady := headerReady.loopBranch allocated.1.1 [first.1] headerBound
        (by simpa [allocated, newBlock1_run] using Nat.lt_succ_of_lt firstBound) (by simpa using firstAfterHeader)
      have bridgeAdv := advB_emitTerm (.br allocated.1.1 [first.1]) le allocated.2 bridged.1 bridged.2 rfl
      let started := (Goose.Lower.setCur (some allocated.1.1) le bridged.2).2
      have headerStill := Nat.lt_of_lt_of_le headerBound bridgeAdv.ext.1
      have startedReady := bridgeReady.setCur (some allocated.1.1) (by intro b row; cases row; exact headerStill)
      have headerGenerated := lastGenerated.newBlock [.data (.int actualType)]
        (rfl : newBlock [.data (.int actualType)] le last.2 = (allocated.1, allocated.2))
      have bridgeGenerated := headerGenerated.emitTerm (.br allocated.1.1 [first.1])
        (by
          intro destination member
          have same : destination = allocated.1.1 := List.mem_singleton.mp member
          subst destination
          exact headerBound)
        (rfl : Goose.Lower.emitTerm (.br allocated.1.1 [first.1]) le allocated.2 = ((), bridged.2))
      have startedGenerated := bridgeGenerated.setCur (some allocated.1.1) (by intro b row; cases row; exact headerStill)
        (rfl : Goose.Lower.setCur (some allocated.1.1) le bridged.2 = ((), started))
      have startEq : nativeRangeStart low high le ls = started := by
        unfold nativeRangeStart
        change (let type := (intTyOf first.1 le last.2).1
          let allocated := newBlock [.data (.int type)] le last.2
          let bridged := Goose.Lower.emitTerm (.br allocated.1.1 [first.1]) le allocated.2
          (Goose.Lower.setCur (some allocated.1.1) le bridged.2).2) = started
        rw [typeRun]
      let bodyAction := fun depth exit => lowerBlock (some ⟨depth, exit, .next allocated.1.1 actualType counter⟩)
        [(variableId, counter, origin)] false body
      have whole : lowerStmt loop (.forRange variableId low high body origin) le ls =
          lowerRange actualType counter last.1 allocated.1.1 bodyAction le started := by
        simp only [lowerStmt, bind_run]
        change whenLive () _ le last.2 = _
        rw [whenLive_some _ _ _ current]
        simp only [bind_run]
        rw [typeRun]
      have nativeRange : NativeRows vt (lowerRange actualType counter last.1 allocated.1.1 bodyAction le started).2 := by rw [whole] at native; exact native
      have rangeProjects := projects
      rw [whole] at rangeProjects
      have rangeContinuation := continuation
      rw [whole] at rangeContinuation
      have metadata : variableId < env.impl.vars.size ∧ origin < env.mod.origins.size := by
        have row := (declare_ok _ _ _ _ _ declaration).2.1
        have variableBound := (Array.getElem?_eq_some_iff.mp row).1
        obtain ⟨_, _, originCheck, _⟩ := (st_bind_ok _ _ _ _).mp source
        exact ⟨by simpa only [tables.variablesEq] using variableBound,
          by simpa only [tables.moduleEq] using ((checkOrg_ok _ _ _ _).mp originCheck).1⟩
      have allocatedAdv := advB_newBlock1 (.data (.int actualType)) le last.2 allocated.1 allocated.2 rfl
      have valueGrowth : last.2.vals.size ≤ started.vals.size := Nat.le_trans allocatedAdv.vals bridgeAdv.vals
      let headerTargets := allocated.1.1 :: siteTargets
      have headerGhostGrowth : lastProv.vals.size ≤ headerProv.vals.size := by
        rw [lastReady.roots.valueSize, headerReady.roots.valueSize]
        exact allocatedAdv.vals
      have headerFresh : last.2.blocks.size ≤ allocated.1.1 := by rw [headerEq]; exact Nat.le_refl _
      have allocatedSites := ((lastSites.reserve allocated.1.1 headerFresh).newBlock [.data (.int actualType)]).ghost_retained
        headerGhostGrowth headerGrowth
      have startedSites : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot headerTargets le started
          (lowerContextAt env.mod env.ctx env.impl) vt headerProv :=
        (allocatedSites.emitTerm (term := .br allocated.1.1 [first.1])
          (by intro target member; exact Or.inl (List.mem_cons.mpr (Or.inl (by simpa [Term.successors] using member)))) rfl).setCur _
      have startedBounds : ReplacementTargetsBound headerTargets started := by
        intro target member
        rcases List.mem_cons.mp member with rfl | previous
        · exact headerStill
        · exact Nat.lt_of_lt_of_le (targetBounds target previous)
            (Nat.le_trans firstAdv.ext.1 (Nat.le_trans lastAdv.ext.1 (Nat.le_trans allocatedAdv.ext.1 bridgeAdv.ext.1)))
      have startedNative := nativeRange.of_prefix (types_lowerRange actualType counter last.1 allocated.1.1
        (fun _ _ => types_lowerBlock _ _ _ _) le started _ _ rfl)
      have allocatedCounterRow : allocated.2.vals[counter]? = some (some (.data (.int actualType))) := by
        simp [counterEq, allocated, newBlock1_run]
      have counterRow : vt[counter]? = some (some (.data (.int actualType))) :=
        startedNative _ _ ((types_emitTerm (.br allocated.1.1 [first.1]) le allocated.2 _ _ rfl) _ _ allocatedCounterRow)
      have counterScalarType : valRefLike vt counter = false := by simp [valRefLike, counterRow, VTy.refLike, Ty.isRefLike]
      have highScalarType : valRefLike vt last.1 = false := by
        apply lastNative.scalar_expression (results := env.impl.results.toList) firstGenerated highTyped ?_ live rfl
        change lowerExpr high (lowerEnv typingEnv.mod typingEnv.vars env.impl.results.toList) first.2 = last
        rw [← tables.moduleEq, ← tables.variablesEq]
      obtain ⟨next, nextReady, growth, transfer, rangeLedger, rangeSites⟩ := canonical_loopRangeOccurrence
        (root := .statement (.forRange variableId low high body origin)) startedReady startedSites startedBounds
        expected actualType counter last.1 allocated.1.1 bodyAction
        (by rfl) headerStill (Nat.lt_of_lt_of_le counterBound bridgeAdv.vals) (Nat.lt_of_lt_of_le lastResult.bound valueGrowth)
        (by simpa only [counterEq] using counterEmpty) counterScalarType highScalarType (by simp [headerTargets]) startedGenerated nativeRange rangeProjects rangeContinuation (fun _ _ => advB_lowerBlock _ _ _ _)
        (by
          intro provenance
          dsimp only
          intro stateReady stateSites stateBounds stateGenerated stateNative headerBound exitBound counterBound counterScalar priorRoots bodyProjects bodyContinuation
          let compared := Goose.Lower.emitDef (.cmp .lt actualType counter last.1) le started
          let split := fork compared.1 le compared.2
          let bodyEntry := nativeRangeBody actualType counter last.1 le started
          have bounds : LoopBuilderTargets (some ⟨compared.2.stack.length, split.1.2, .next allocated.1.1 actualType counter⟩) bodyEntry := ⟨exitBound, headerBound⟩
          have replayBounds : LoopReplayBounds (some ⟨compared.2.stack.length, split.1.2, .next allocated.1.1 actualType counter⟩)
              scopeCount bodyEntry := by
            refine ⟨counterBound, ?_⟩
            change ∀ entered ∈ (loopBodyEntry compared.1 le compared.2).stack.take
              ((loopBodyEntry compared.1 le compared.2).stack.length - compared.2.stack.length), entered < scopeCount
            rw [native_loopBody_entry_stack]
            simp
          obtain ⟨next, nextReady, _, retained, transfer, bodyLedger, bodySites⟩ := bodyChild
            (split.1.2 :: headerTargets) compared.2.stack.length allocated.1.1 split.1.2 actualType counter bodyEntry provenance
            (by change actualType = (intTyOf first.1 le last.2).1; rw [typeRun]) headerEq counterEq
            (by change bodyEntry = nativeRangeBody actualType counter last.1 le (nativeRangeStart low high le ls); rw [startEq])
            bodySource (by
              obtain ⟨path, located⟩ := sourceCursor
              refine ⟨path ++ [2], located.child ?_⟩
              have sourceChild := canonical_range_body_child le ls loop variableId low high body origin live
              have typeEq : (intTyOf (lowerExpr low le ls).1 le
                  (lowerExpr high le (lowerExpr low le ls).2).2).1 = actualType := by
                change (intTyOf first.1 le last.2).1 = actualType
                rw [typeRun]
              simpa only [typeEq, startEq] using sourceChild) bodyType highFinish finish highState after bodyRoots bodyRange bodyTyped bodyReplay wholeEffect scopes
            (by simpa using metadata)
            (by intro _ binding member; have same := List.mem_singleton.mp member; subst binding; exact counterBound)
            (by intro binding member root rootMember; have same := List.mem_singleton.mp member; subst binding; rw [counterScalar] at rootMember; cases rootMember)
            (by
              intro plain entered member
              apply stackBounds plain entered
              rw [native_range_body_stack] at member
              change entered ∈ bridged.2.stack at member
              rw [bridgeAdv.stack, allocatedAdv.stack, lastAdv.stack, firstAdv.stack] at member
              exact member)
            stateReady stateSites stateBounds stateGenerated bounds replayBounds counterRow
            (by
              intro target member
              change target ∈ [split.1.2, allocated.1.1] at member
              rcases List.mem_cons.mp member with first | rest
              · exact List.mem_cons.mpr (Or.inl first)
              · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp rest))))
            stateNative bodyProjects bodyContinuation
          exact ⟨next, nextReady, retained, transfer, bodyLedger.underRoot bodyAt, bodySites⟩)
      have headerReturns : ReturnMembershipFrame last.2 started := by
        apply ReturnFrameRun.of_absence (fun _ => ReturnFrames.returnAbsent_header1 (.data (.int actualType)) first.1 (fun _ _ => ReturnFrames.returnAbsent_pure ()))
          le last.2 () started
        simp only [bind_run, pure_run]
        rfl
      have headerTransfer : ReturnBoundsPreserved expected last.2 lastProv started headerProv :=
        .frame lastReady.symbols lastReady.roots.valueSize headerGrowth headerReturns
      refine ⟨next, by rw [whole]; exact nextReady, ?_, ?_, ?_, ?_⟩
      · intro old bound
        have lastBound : old < lastProv.vals.size := by
          rw [lastReady.roots.valueSize]
          exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) (Nat.le_trans firstAdv.vals lastAdv.vals)
        have headerBound : old < headerProv.vals.size := by
          rw [startedReady.roots.valueSize]
          exact Nat.lt_of_lt_of_le (by simpa only [lastReady.roots.valueSize] using lastBound) valueGrowth
        rw [growth old headerBound, headerGrowth old lastBound, oldGrowth old bound]
      · rw [whole]
        exact firstTransfer.trans (lastTransfer.trans (headerTransfer.trans transfer))
      · rw [whole]
        have rangeGrowth : headerProv.vals.size ≤ next.vals.size := by
          rw [startedReady.roots.valueSize, nextReady.roots.valueSize]
          exact (advB_lowerRange actualType counter last.1 allocated.1.1 (fun _ _ => advB_lowerBlock _ _ _ _) le started _ _ rfl).vals
        have headerPrefix : ∀ old, old < lastProv.vals.size → rootsAt next.vals old = rootsAt lastProv.vals old := by
          intro old bound
          exact (growth old (Nat.lt_of_lt_of_le bound headerGhostGrowth)).trans (headerGrowth old bound)
        have headerLedger : OccurrenceLedger env (.statement (.forRange variableId low high body origin))
            (lowerContextAt env.mod env.ctx env.impl) vt next last.2 started :=
          (emitsOnly_newBlock _ _ le last.2 _ _ rfl).trans
            ((emitsOnly_emitTerm _ (occurrenceInstructionTerm _) le allocated.2 _ _ rfl).trans (.of_blocks rfl))
        exact ((expressionsLedger.retained (Nat.le_trans headerGhostGrowth rangeGrowth) headerPrefix).trans headerLedger).trans rangeLedger
      · rw [whole]
        exact rangeSites.weaken (by intro target member; exact List.mem_cons_of_mem _ member)


theorem canonical_statementOccurrence_range {typingEnv : TEnv} {env : PEnv}
    {variableId : VarId} {low high : Expr} {body : Core.Block} {origin : OriginId}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId}
    {loop : Option LoopCtx} {scope : ScopeId} {initial : LS} {upper : Prov}
    (tables : SourceRootTables typingEnv env)
    (lowChild : CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets low initial upper)
    (highChild : ∀ provenance, CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets high
      (lowerExpr low (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 provenance)
    (bodyChild : ∀ targets depth header exit type counter state provenance,
      let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
      let first := lowerExpr low le initial
      let last := lowerExpr high le first.2
      type = (intTyOf first.1 le last.2).1 → header = last.2.blocks.size → counter = last.2.vals.size →
      state = nativeRangeBody type counter last.1 le (nativeRangeStart low high le initial) →
      CanonicalBlockOccurrenceReplayAt ownerRoot ownerInitial baseline {typingEnv with loops := typingEnv.loops + 1, visible := variableId :: typingEnv.visible}
        env results vt target scopeCount siteRoot targets (some ⟨depth, exit, .next header type counter⟩)
        [(variableId, counter, origin)] false body state provenance) :
    CanonicalStatementOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets loop scope
      (.forRange variableId low high body origin) initial upper := by
  intro location sourceCursor output start finish before after typed replay ceiling scopes stack ready sites targetBounds
    generated loopTargets loopReplay counterTyped included native projects continuation
  have bodyScopes : SourceScopesWithin scopeCount (Core.blockScopes none body) := by
    apply scopes.of_subset
    intro entry member
    exact List.mem_append_right _ member
  exact canonical_typedRangeOccurrence loop tables location sourceCursor typed replay ceiling bodyScopes stack ready sites targetBounds
    generated native projects continuation lowChild highChild bodyChild

#print axioms canonical_statementOccurrence_range

end Goose.Lower.Validation.SourceReplacementWriterLedger
