import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceStorageAssign
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessReadLocal

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation ReplacementContentFlowSource

theorem canonical_statementOccurrence_assign {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
    {ownerRoot : Fragment} {ownerInitial baseline : LS}
    {siteRoot : DemandNode} {siteTargets : List BlockId}
    {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)}
    {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}
    {place : Place} {expression : Expr} (origin : OriginId) (loop : Option LoopCtx) (scope : ScopeId)
    (tables : SourceRootTables typingEnv env) (closed : ParameterRootsClosed func)
    (referencePlace : ReferenceSlicePlaceOccurrenceReplayAt env results vt func returnTypes slots target scopeCount siteRoot siteTargets initial upper)
    (placeChild : CanonicalGlobalPlaceOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets place initial upper)
    (valueChild : ∀ provenance, CanonicalGlobalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets expression
      (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).2 provenance) :
    CanonicalGlobalStatementOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets loop scope (.assign place expression origin) initial upper := by
  intro occurrence cursor output start finish before after typed replay ceiling _sourceScopes _stack ready sites targets generated _loopTargets _loopReplay _counter _included native metadata continuation
  obtain ⟨path, globalPath⟩ := occurrence
  obtain ⟨actualPath, located⟩ := cursor
  obtain ⟨info, childStart, placeTyped, valueTyped, shape, _writable, _⟩ := tyStmt_assign_children typed
  obtain ⟨placeRoots, placeState, placeReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  obtain ⟨valueRoots, valueState, valueReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp tail
  have sourceEffect := (rpStmt_assign_contract placeReplay valueReplay replay).2
  have valueCeiling : EffectRefinement func valueState.eff target := by
    apply EffectRefinement.trans (middle := after.eff) ?_ ceiling
    rw [sourceEffect]
    refine ⟨fun _ h => h, ?_, fun _ h => h, fun _ h => h, ?_, fun h => h, fun h => h, fun h => h⟩
    · exact storageTargets_mono (fun t h => addTargets_left _ _ t h)
    · exact fun t h => addTargets_left _ _ t h
  have placeCeiling := effectRefinement_before_expression valueReplay valueCeiling
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let address := lowerPlace place le initial
  let value := lowerExpr expression le address.2
  have valueNative : NativeRows vt value.2 := native.of_prefix
    (types_emitEffect (.store address.1 value.1 (some origin)) le value.2 _ _ rfl)
  have valueMetadata := metadata.of_advance
    (advB_emitEffect (.store address.1 value.1 (some origin)) le value.2 _ _ rfl)
  have valueContinuation := continuation.of_advance
    (advB_emitEffect (.store address.1 value.1 (some origin)) le value.2 _ _ rfl)
  have placeNative := valueNative.of_prefix (types_lowerExpr expression le address.2 _ _ rfl)
  have placeMetadata := valueMetadata.of_advance (advB_lowerExpr expression le address.2 _ _ rfl)
  have placeContinuation := valueContinuation.of_advance (advB_lowerExpr expression le address.2 _ _ rfl)
  have classified := mutation_assign_source_cases tables placeTyped shape
  have ownerPackage : ∃ middle,
      ReplayBuilder (lower env.mod) results vt func target le scopeCount
        slots address.2 middle ∧
      (address.2.cur.isSome = true → address.1 < address.2.vals.size ∧
        GIR.RootsRefine func (rootsAt middle.vals address.1) placeRoots) ∧
      (∀ old, old < upper.vals.size → rootsAt middle.vals old = rootsAt upper.vals old) ∧
      (info.ty.isRefLike = false ∨ ∃ parameter,
        place.derefVar? = some parameter ∧ env.isRefSliceVar parameter = true ∧ parameter < env.impl.params.size ∧
        (address.2.cur.isSome = true → ∀ root ∈ rootsAt middle.vals address.1, root ∈ [RootRef.param parameter])) ∧
      OccurrenceLedger env (.place place) func vt middle initial address.2 ∧
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le address.2 func vt middle := by
    rcases classified with nonref | ⟨parameter, localVar, placeEq, variableRow, reference⟩
    · obtain ⟨middle, placeReady, placeValue, placePrefix, placeLedger, placeSites⟩ := placeChild ⟨path ++ [0], globalPath.snoc 0 rfl⟩ ⟨actualPath ++ [0], located.child rfl⟩ info start childStart before placeState placeRoots
        placeTyped placeReplay placeCeiling ready sites targets generated placeNative placeMetadata placeContinuation
      exact ⟨middle, placeReady, placeValue, placePrefix, Or.inl nonref, placeLedger, placeSites⟩
    · subst place
      obtain ⟨bound, refSlice, middle, placeReady, placeValue, placePrefix, placeLedger, oldPlaceSites⟩ :=
        referencePlace _ _ variableRow reference _ _ _ placeReplay ready sites.toOld placeMetadata
      let addressed := lowerPlace (.var parameter) le initial
      have emitted : EmitsOnly NotReplacement initial
          (lowerPlace (.deref (.read (.var parameter))) le initial).2 :=
        ((emitsOnly_emitDef (rfl : emitDef (.slotAddr parameter) le initial = addressed) trivial).trans
          (emitsOnly_emitDef (rfl : emitDef (.load addressed.1) le addressed.2 = _) trivial)).trans
          (.of_blocks (ReplayBuilder.readBlocks_eq (.var parameter) le initial))
      have placeSites := sites.of_emits emitted
        (types_lowerPlace (.deref (.read (.var parameter))) le initial _ _ rfl)
        (.of_run (generatedTargetFrame_lowerPlace none (.deref (.read (.var parameter)))) rfl)
        (accessRootsGrowth ready placeReady (advB_lowerPlace (.deref (.read (.var parameter))) le initial _ _ rfl).vals) placePrefix
      obtain ⟨contents, observed, _⟩ := Core.Sound.checkStore_ok env _ valueRoots
        (rpStmt_assign_contract placeReplay valueReplay replay).1 parameter rfl refSlice
      have observedSome : (env.cont parameter).isSome = true := by simp [observed]
      exact ⟨middle, placeReady, fun live => ⟨(placeValue live).1, (placeValue live).2.1⟩,
        placePrefix, Or.inr ⟨parameter, rfl, refSlice, bound, fun live => (placeValue live).2.2.1 observedSome⟩, placeLedger, placeSites⟩
  obtain ⟨middle, placeReady, placeValue, placePrefix, storeCase, placeLedger, placeSites⟩ := ownerPackage
  obtain ⟨next, valueReady, valueFacts, valuePrefix, valueLedger, valueSites⟩ := valueChild middle ⟨path ++ [1], globalPath.snoc 1 rfl⟩ ⟨actualPath ++ [1], located.child rfl⟩ info.ty childStart finish placeState valueState valueRoots
    valueTyped valueReplay valueCeiling placeReady placeSites (targets.mono (advB_lowerPlace place le initial _ _ rfl).ext) (generated.lowerPlace place rfl) valueNative valueMetadata valueContinuation
  have retained (old : Nat) (bound : old < upper.vals.size) : rootsAt next.vals old = rootsAt upper.vals old := by
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, placeReady.roots.valueSize]
      exact (advB_lowerPlace place le initial _ _ rfl).vals
    exact (valuePrefix old (Nat.lt_of_lt_of_le bound growth)).trans (placePrefix old bound)
  have completed : ReplayBuilder (lower env.mod) results vt func target le scopeCount
      slots (lowerStmt loop (.assign place expression origin) le initial).2 next := by
    rcases storeCase with nonref | ⟨parameter, deref, reference, parameterBound, identity⟩
    · apply valueReady.assignNonref loop placeReplay valueReplay replay ceiling rfl rfl
        closed (tables.mutation_origin_bound typed)
      intro live
      have placeLive := (dead_lowerExpr expression).live_before rfl live
      have placeBound := (placeValue placeLive).1
      refine ⟨Nat.lt_of_lt_of_le placeBound (advB_lowerExpr expression le address.2 _ _ rfl).vals,
        (valueFacts live).bound, ?_, ?_, (valueFacts live).scalar nonref⟩
      · rw [valuePrefix address.1 (by rw [placeReady.roots.valueSize]; exact placeBound)]
        exact (placeValue placeLive).2
      · obtain ⟨mu, row⟩ := tables.occurrence_native_place_row placeNative generated placeTyped rfl placeLive
        simpa [ownerTy, row] using nonref
    · apply valueReady.assignRefSlice loop placeReplay valueReplay replay ceiling rfl rfl
        closed (tables.mutation_origin_bound typed)
        deref reference parameterBound
      intro live
      have placeLive := (dead_lowerExpr expression).live_before rfl live
      have placeBound := (placeValue placeLive).1
      refine ⟨Nat.lt_of_lt_of_le placeBound (advB_lowerExpr expression le address.2 _ _ rfl).vals,
        (valueFacts live).bound, ?_, ?_⟩
      · rw [valuePrefix address.1 (by rw [placeReady.roots.valueSize]; exact placeBound)]
        exact (placeValue placeLive).2
      · rw [valuePrefix address.1 (by rw [placeReady.roots.valueSize]; exact placeBound)]
        exact identity placeLive
  have growth : middle.vals.size ≤ next.vals.size := by
    rw [placeReady.roots.valueSize, valueReady.roots.valueSize]
    exact (advB_lowerExpr expression le address.2 _ _ rfl).vals
  have placePath : DemandNodeAt (.statement (.assign place expression origin)) [0] (.place place) := .child rfl (.here _)
  have valuePath : DemandNodeAt (.statement (.assign place expression origin)) [1] (.expression expression) := .child rfl (.here _)
  have step := occurrence_emitEffect_live (env := env) (root := .statement (.assign place expression origin))
    (func := func) (types := vt) (upper := next)
    (rfl : emitEffect (.store address.1 value.1 (some origin)) le value.2 = _) (by
      intro live
      refine InstructionOccurrences.store ?_ ?_ ?_
      · intro operand member _
        have same : operand = address.1 := by simpa [GIR.ReplacementContentFlow.Model.accessOperands] using member
        subst operand
        have placeLive := (dead_lowerExpr expression).live_before rfl live
        have oldBound : address.1 < middle.vals.size := placeReady.roots.valueSize ▸ (placeValue placeLive).1
        apply OperandOccurrence.place placePath placeReplay (Nat.lt_of_lt_of_le oldBound growth)
        rw [valuePrefix address.1 oldBound]
        exact (placeValue placeLive).2
      · intro reference
        rcases storeCase with nonref | ⟨parameter, deref, isRef, parameterBound, identity⟩
        · have row : vt[value.1]? = some (some (.data info.ty)) :=
            tables.occurrence_native_expression_row valueNative (generated.lowerPlace place (env := le) rfl) valueTyped
              (rfl : lowerExpr expression le address.2 = value) live
          simp only [valRefLike, row, VTy.refLike, nonref] at reference
          cases reference
        · have placeLive := (dead_lowerExpr expression).live_before rfl live
          have oldBound : address.1 < middle.vals.size := placeReady.roots.valueSize ▸ (placeValue placeLive).1
          refine Or.inl ⟨{
            localEnv := env
            access := rfl
            path := []
            place := place
            expression := expression
            sourceOrigin := origin
            origin_eq := rfl
            source := .here _
            before := before
            placeRoots := placeRoots
            placeAfter := placeState
            valueRoots := valueRoots
            after := valueState
            placeReplay := placeReplay
            valueReplay := valueReplay
            checked := (rpStmt_assign_contract placeReplay valueReplay replay).1
            addressBound := Nat.lt_of_lt_of_le oldBound growth
            valueBound := valueReady.roots.valueSize ▸ (valueFacts live).bound
            addressRefined := by rw [valuePrefix address.1 oldBound]; exact (placeValue placeLive).2
            formalAddress := by
              intro variableId same _ root member
              rw [same] at deref
              have identityIndex : variableId = parameter := Option.some.inj deref
              subst variableId
              rw [valuePrefix address.1 oldBound] at member
              exact identity placeLive root member
            valueRefined := (valueFacts live).refined
            referenceTarget := ⟨parameter, Core.Sound.derefVar_eq deref, isRef⟩ }⟩
      · intro operand member _ _ _
        have same : operand = address.1 := by simpa [GIR.ReplacementContentFlow.Model.accessOperands] using member
        subst operand
        have placeLive := (dead_lowerExpr expression).live_before rfl live
        have oldBound : address.1 < middle.vals.size := placeReady.roots.valueSize ▸ (placeValue placeLive).1
        refine .place address.1 env [0] place before placeRoots placeState rfl placePath placeReplay
          (Nat.lt_of_lt_of_le oldBound growth) ?_
        rw [valuePrefix address.1 oldBound]
        exact (placeValue placeLive).2)

  have ledger := ((placeLedger.retained growth valuePrefix).underRoot placePath).trans
    ((valueLedger.underRoot valuePath).trans step)
  have finalSites := valueSites.mutationEffect (effect := .store address.1 value.1 (some origin)) trivial rfl
    (Nat.le_refl _) (fun _ _ => rfl)
  exact ⟨next, completed, retained, (fun expected => occurrence_mutation_transfer loop typed rfl ready retained), ledger, finalSites⟩


#print axioms canonical_statementOccurrence_assign

end Goose.Lower.Validation.SourceReplacementWriterLedger
