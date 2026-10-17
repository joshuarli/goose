import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceMutationsActions
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceMutationsCommon

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation ReplacementContentFlowSource

private theorem fill_extension (func : Func) (source : Core.Eff) (roots : List RootRef) :
    EffectRefinement func source {source with
      reads := addTargets source.reads (rootsTargets roots)
      writes := addTargets source.writes (rootsTargets roots)
      grows := addTargets source.grows (rootsTargets roots)
      shrinks := addTargets source.shrinks (rootsTargets roots)
      aborts := true} := by
  refine ⟨?_, ?_, ?_, ?_, fun _ h => h, fun _ => rfl, fun h => h, fun h => h⟩
  all_goals exact storageTargets_mono (fun target member => addTargets_left _ _ target member)

theorem canonical_statementOccurrence_resizeWithFill {ownerRoot : Fragment} {ownerInitial baseline : LS} {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
    {siteRoot : DemandNode} {siteTargets : List BlockId}
    {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}
    {owner : Place} {size fill : Expr} (origin : OriginId) (loop : Option LoopCtx) (scope : ScopeId)
    (tables : SourceRootTables typingEnv env) (readable : SourceReadableEnvironment typingEnv) (closed : ParameterRootsClosed func)
    (ownerChild : CanonicalGlobalPlaceOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets owner initial upper)
    (sizeChild : ∀ provenance, CanonicalGlobalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets size
      (lowerPlace owner (lowerEnv env.mod env.impl.vars returnTypes) initial).2 provenance)
    (fillChild : ∀ provenance, CanonicalGlobalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets fill
      (lowerExpr size (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerPlace owner (lowerEnv env.mod env.impl.vars returnTypes) initial).2).2 provenance) :
    CanonicalGlobalStatementOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets loop scope (.resize owner size (some fill) origin) initial upper := by
  intro occurrence cursor output start finish before after typed replay ceiling _sourceScopes _stack ready sites targets generated _loopTargets _loopReplay _counterTyped _included native metadata continuation
  obtain ⟨path, globalPath⟩ := occurrence
  obtain ⟨actualPath,located⟩ := cursor
  obtain ⟨info, element, integer, childStart, sizeFinish, ownerTyped, _elementType, sizeTyped, fillTyped, _writable, _⟩ :=
    tyStmt_resize_children typed
  obtain ⟨ownerRoots, ownerState, ownerReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  obtain ⟨sizeRoots, sizeState, sizeReplay, tail⟩ := (st_bind_ok _ _ _ _).mp tail
  obtain ⟨fillRoots, fillState, fillReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp tail
  have sourceEffect := rpStmt_resize_fill_effect ownerReplay sizeReplay fillReplay replay
  have fillCeiling : EffectRefinement func fillState.eff target := by
    apply (fill_extension _ _ ownerRoots).trans
    simpa only [sourceEffect] using ceiling
  have sizeCeiling := effectRefinement_before_expression fillReplay fillCeiling
  have ownerCeiling := effectRefinement_before_expression sizeReplay sizeCeiling
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let address := lowerPlace owner le initial
  let amount := lowerExpr size le address.2
  let value := lowerExpr fill le amount.2
  have fillNative : NativeRows vt value.2 := native.of_prefix
    (types_emitEffect (.resize address.1 amount.1 (some value.1) (some origin)) le value.2 _ _ rfl)
  have fillMetadata := metadata.of_advance
    (advB_emitEffect (.resize address.1 amount.1 (some value.1) (some origin)) le value.2 _ _ rfl)
  have fillContinuation := continuation.of_advance
    (advB_emitEffect (.resize address.1 amount.1 (some value.1) (some origin)) le value.2 _ _ rfl)
  have sizeNative := fillNative.of_prefix (types_lowerExpr fill le amount.2 _ _ rfl)
  have sizeMetadata := fillMetadata.of_advance (advB_lowerExpr fill le amount.2 _ _ rfl)
  have sizeContinuation := fillContinuation.of_advance (advB_lowerExpr fill le amount.2 _ _ rfl)
  have ownerNative := sizeNative.of_prefix (types_lowerExpr size le address.2 _ _ rfl)
  have ownerMetadata := sizeMetadata.of_advance (advB_lowerExpr size le address.2 _ _ rfl)
  have ownerContinuation := sizeContinuation.of_advance (advB_lowerExpr size le address.2 _ _ rfl)
  obtain ⟨ownerUpper, ownerReady, ownerValue, ownerPrefix, ownerLedger, ownerSites⟩ :=
    ownerChild ⟨path ++ [0], globalPath.snoc 0 rfl⟩ ⟨actualPath ++ [0],located.child rfl⟩ info start childStart before ownerState ownerRoots ownerTyped ownerReplay ownerCeiling ready sites targets generated ownerNative ownerMetadata ownerContinuation
  have ownerGenerated := generated.lowerPlace owner (env := le) rfl
  obtain ⟨sizeUpper, sizeReady, sizeValue, sizePrefix, sizeLedger, sizeSites⟩ :=
    sizeChild ownerUpper ⟨path ++ [1], globalPath.snoc 1 rfl⟩ ⟨actualPath ++ [1],located.child rfl⟩ (.int integer) childStart sizeFinish ownerState sizeState sizeRoots sizeTyped sizeReplay sizeCeiling
      ownerReady ownerSites (targets.mono (advB_lowerPlace owner le initial _ _ rfl).ext) ownerGenerated sizeNative sizeMetadata sizeContinuation
  obtain ⟨next, fillReady, fillValue, fillPrefix, fillLedger, fillSites⟩ :=
    fillChild sizeUpper ⟨path ++ [2], globalPath.snoc 2 rfl⟩ ⟨actualPath ++ [2],located.child rfl⟩ element sizeFinish finish sizeState fillState fillRoots fillTyped fillReplay fillCeiling
      sizeReady sizeSites ((targets.mono (advB_lowerPlace owner le initial _ _ rfl).ext).mono
        (advB_lowerExpr size le address.2 _ _ rfl).ext) (ownerGenerated.lowerExpr size rfl) fillNative fillMetadata fillContinuation
  have sizeGrowth := advB_lowerExpr size le address.2 amount.1 amount.2 rfl
  have fillGrowth := advB_lowerExpr fill le amount.2 value.1 value.2 rfl
  have completed := fillReady.resizeWithFill loop ownerReplay sizeReplay fillReplay replay ceiling rfl rfl rfl
    closed
    (tables.mutation_origin_bound typed) (by
      intro live
      have sizeLive := (dead_lowerExpr fill).live_before rfl live
      have ownerLive := (dead_lowerExpr size).live_before rfl sizeLive
      have oldBound := (ownerValue ownerLive).1
      have addressMiddle := Nat.lt_of_lt_of_le oldBound sizeGrowth.vals
      refine ⟨Nat.lt_of_lt_of_le addressMiddle fillGrowth.vals,
        Nat.lt_of_lt_of_le (sizeValue sizeLive).bound fillGrowth.vals, (fillValue live).bound, ?_⟩
      rw [fillPrefix address.1 (by rw [sizeReady.roots.valueSize]; exact addressMiddle),
        sizePrefix address.1 (by rw [ownerReady.roots.valueSize]; exact oldBound)]
      exact (ownerValue ownerLive).2)
  have retained (old : Nat) (bound : old < upper.vals.size) : rootsAt next.vals old = rootsAt upper.vals old := by
    have ownerGrowth : upper.vals.size ≤ ownerUpper.vals.size := by
      rw [ready.roots.valueSize, ownerReady.roots.valueSize]
      exact (advB_lowerPlace owner le initial _ _ rfl).vals
    have ownerBound := Nat.lt_of_lt_of_le bound ownerGrowth
    have sizeBound : old < sizeUpper.vals.size := by
      rw [sizeReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (ownerReady.roots.valueSize ▸ ownerBound) sizeGrowth.vals
    exact (fillPrefix old sizeBound).trans ((sizePrefix old ownerBound).trans (ownerPrefix old bound))
  have ownerGrowth : ownerUpper.vals.size ≤ sizeUpper.vals.size := by
    rw [ownerReady.roots.valueSize, sizeReady.roots.valueSize]
    exact sizeGrowth.vals
  have sizeToFill : sizeUpper.vals.size ≤ next.vals.size := by
    rw [sizeReady.roots.valueSize, fillReady.roots.valueSize]
    exact fillGrowth.vals
  have placePath : DemandNodeAt (.statement (.resize owner size (some fill) origin)) [0] (.place owner) := .child rfl (.here _)
  have sizePath : DemandNodeAt (.statement (.resize owner size (some fill) origin)) [1] (.expression size) := .child rfl (.here _)
  have fillPath : DemandNodeAt (.statement (.resize owner size (some fill) origin)) [2] (.expression fill) := .child rfl (.here _)
  have step := occurrence_emitEffect_live (env := env) (root := .statement (.resize owner size (some fill) origin))
    (func := func) (types := vt) (upper := next)
    (rfl : emitEffect (.resize address.1 amount.1 (some value.1) (some origin)) le value.2 = _) (by
      intro live
      apply InstructionOccurrences.effect (ordinary := by intro address value origin same; cases same)
        (consumed := by
          intro operand member mutability payload reference
          have alternatives : operand = address.1 ∨ operand = amount.1 ∨ operand = value.1 := by
            simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Effect.uses] using member
          rcases alternatives with same | same | same
          · subst operand
            have sizeLive := (dead_lowerExpr fill).live_before rfl live
            have ownerLive := (dead_lowerExpr size).live_before rfl sizeLive
            have oldBound : address.1 < ownerUpper.vals.size := ownerReady.roots.valueSize ▸ (ownerValue ownerLive).1
            have middleBound := Nat.lt_of_lt_of_le oldBound ownerGrowth
            refine .place address.1 env [0] owner before ownerRoots ownerState rfl placePath ownerReplay
              (Nat.lt_of_lt_of_le middleBound sizeToFill) ?_
            rw [fillPrefix address.1 middleBound, sizePrefix address.1 oldBound]
            exact (ownerValue ownerLive).2
          · subst operand
            have row := tables.occurrence_native_expression_row sizeNative ownerGenerated sizeTyped
              (rfl : lowerExpr size le address.2 = amount) ((dead_lowerExpr fill).live_before rfl live)
            rw [row] at reference
            cases reference
          · subst operand
            have row := tables.occurrence_native_expression_row fillNative (ownerGenerated.lowerExpr size rfl) fillTyped
              (rfl : lowerExpr fill le amount.2 = value) live
            have allowed := source_place_paramOk owner readable ownerTyped
            have flat : element.flat = true := occurrence_owner_element_flat allowed _elementType
            rw [row] at reference
            have shape : element = .ref mutability payload := VTy.data.inj (Option.some.inj (Option.some.inj reference))
            simp [shape, Ty.flat] at flat)
      intro operand member _
      have alternatives : operand = address.1 ∨ operand = amount.1 ∨ operand = value.1 := by
        simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Effect.uses] using member
      rcases alternatives with same | same | same
      · subst operand
        have sizeLive := (dead_lowerExpr fill).live_before rfl live
        have ownerLive := (dead_lowerExpr size).live_before rfl sizeLive
        have oldBound : address.1 < ownerUpper.vals.size := ownerReady.roots.valueSize ▸ (ownerValue ownerLive).1
        have middleBound := Nat.lt_of_lt_of_le oldBound ownerGrowth
        apply OperandOccurrence.place placePath ownerReplay (Nat.lt_of_lt_of_le middleBound sizeToFill)
        rw [fillPrefix address.1 middleBound, sizePrefix address.1 oldBound]
        exact (ownerValue ownerLive).2
      · subst operand
        have sizeLive := (dead_lowerExpr fill).live_before rfl live
        have middleBound : amount.1 < sizeUpper.vals.size := sizeReady.roots.valueSize ▸ (sizeValue sizeLive).bound
        apply OperandOccurrence.expression sizePath sizeReplay (Nat.lt_of_lt_of_le middleBound sizeToFill)
        rw [fillPrefix amount.1 middleBound]
        exact (sizeValue sizeLive).refined
      · subst operand
        exact OperandOccurrence.expression fillPath fillReplay
          (fillReady.roots.valueSize ▸ (fillValue live).bound) (fillValue live).refined)
  have ledger := (((ownerLedger.retained ownerGrowth sizePrefix).retained sizeToFill fillPrefix).underRoot placePath).trans
    (((sizeLedger.retained sizeToFill fillPrefix).underRoot sizePath).trans ((fillLedger.underRoot fillPath).trans step))
  have finalSites := fillSites.mutationEffect (effect := .resize address.1 amount.1 (some value.1) (some origin)) trivial
    (rfl : emitEffect (.resize address.1 amount.1 (some value.1) (some origin)) le value.2 = _)
    (Nat.le_refl _) (fun _ _ => rfl)
  exact ⟨next, completed, retained, fun expected => occurrence_mutation_transfer loop typed rfl ready retained, ledger, finalSites⟩

end Goose.Lower.Validation.SourceReplacementWriterLedger
