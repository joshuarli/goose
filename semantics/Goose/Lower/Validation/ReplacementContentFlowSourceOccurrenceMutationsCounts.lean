import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceMutationsActions
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceMutationsCommon

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {siteRoot : DemandNode} {siteTargets : List BlockId}
  {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}

theorem statementOccurrence_popN {owner : Place} {count : Expr} (origin : OriginId) (loop : Option LoopCtx) (scope : ScopeId)
    (tables : SourceRootTables typingEnv env) (closed : ParameterRootsClosed func)
    (ownerChild : GlobalPlaceOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets owner initial upper)
    (countChild : ∀ provenance, GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets count
      (lowerPlace owner (lowerEnv env.mod env.impl.vars returnTypes) initial).2 provenance) :
    GlobalStatementOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets loop scope (.popN owner count origin) initial upper := by
  intro occurrence output start finish before after typed replay ceiling _sourceScopes _stack ready sites targets generated _loopTargets _loopReplay _counterTyped _included native metadata continuation
  obtain ⟨path, globalPath⟩ := occurrence
  obtain ⟨info, element, integer, childStart, ownerTyped, _elementType, countTyped, _writable, _⟩ := tyStmt_popN_children typed
  obtain ⟨ownerRoots, ownerState, ownerReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  obtain ⟨countRoots, countState, countReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp tail
  have sourceReplay := replay
  have sourceEffect := rpStmt_popN_effect ownerReplay countReplay sourceReplay
  have countCeiling : EffectRefinement func countState.eff target := by
    apply (mutation_read_shrink_aborts_extension _ _ ownerRoots).trans
    simpa only [sourceEffect] using ceiling
  have ownerCeiling := effectRefinement_before_expression countReplay countCeiling
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let address := lowerPlace owner le initial
  let amount := lowerExpr count le address.2
  have countNative : NativeRows vt amount.2 := by
    apply native.of_prefix
    exact types_emitEffect (.popN address.1 amount.1 (some origin)) le amount.2 _ _ rfl
  have countMetadata : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func amount.2 := by
    apply metadata.of_advance
    exact advB_emitEffect (.popN address.1 amount.1 (some origin)) le amount.2 _ _ rfl
  have countContinuation : NativeBuilderContinuation func amount.2 := by
    apply continuation.of_advance
    exact advB_emitEffect (.popN address.1 amount.1 (some origin)) le amount.2 _ _ rfl
  have ownerNative := countNative.of_prefix (types_lowerExpr count le address.2 _ _ rfl)
  have ownerMetadata := countMetadata.of_advance (advB_lowerExpr count le address.2 _ _ rfl)
  have ownerContinuation := countContinuation.of_advance (advB_lowerExpr count le address.2 _ _ rfl)
  obtain ⟨middle, ownerReady, ownerValue, ownerPrefix, ownerLedger, ownerSites⟩ :=
    ownerChild ⟨path ++ [0], globalPath.snoc 0 rfl⟩ info start childStart before ownerState ownerRoots ownerTyped ownerReplay ownerCeiling ready sites targets generated ownerNative ownerMetadata ownerContinuation
  obtain ⟨next, countReady, countValue, countPrefix, countLedger, countSites⟩ :=
    countChild middle ⟨path ++ [1], globalPath.snoc 1 rfl⟩ (.int integer) childStart finish ownerState countState countRoots countTyped countReplay countCeiling
      ownerReady ownerSites (targets.mono (advB_lowerPlace owner le initial _ _ rfl).ext) (generated.lowerPlace owner rfl) countNative countMetadata countContinuation
  have completed := countReady.popN loop ownerReplay countReplay replay ceiling rfl rfl
    closed
    (tables.mutation_origin_bound typed) (by
      intro live
      have ownerLive := (dead_lowerExpr count).live_before rfl live
      have oldBound := (ownerValue ownerLive).1
      have addressBound := Nat.lt_of_lt_of_le oldBound (advB_lowerExpr count le address.2 _ _ rfl).vals
      refine ⟨addressBound, (countValue live).bound, ?_⟩
      rw [countPrefix address.1 (by rw [ownerReady.roots.valueSize]; exact oldBound)]
      exact (ownerValue ownerLive).2)
  have retained (old : Nat) (bound : old < upper.vals.size) : rootsAt next.vals old = rootsAt upper.vals old := by
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, ownerReady.roots.valueSize]
      exact (advB_lowerPlace owner le initial _ _ rfl).vals
    exact (countPrefix old (Nat.lt_of_lt_of_le bound growth)).trans (ownerPrefix old bound)
  have growth : middle.vals.size ≤ next.vals.size := by
    rw [ownerReady.roots.valueSize, countReady.roots.valueSize]
    exact (advB_lowerExpr count le address.2 _ _ rfl).vals
  have placePath : DemandNodeAt (.statement (.popN owner count origin)) [0] (.place owner) := .child rfl (.here _)
  have countPath : DemandNodeAt (.statement (.popN owner count origin)) [1] (.expression count) := .child rfl (.here _)
  have step := occurrence_emitEffect_live (env := env) (root := .statement (.popN owner count origin))
    (func := func) (types := vt) (upper := next)
    (rfl : emitEffect (.popN address.1 amount.1 (some origin)) le amount.2 = _) (by
      intro live
      apply InstructionOccurrences.effect (ordinary := by intro address value origin same; cases same)
        (consumed := by
          intro value member mutability payload reference
          have alternatives : value = address.1 ∨ value = amount.1 := by
            simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Effect.uses] using member
          rcases alternatives with same | same
          · subst value
            have ownerLive := (dead_lowerExpr count).live_before rfl live
            have bounded : address.1 < middle.vals.size := ownerReady.roots.valueSize ▸ (ownerValue ownerLive).1
            refine .place address.1 env [0] owner before ownerRoots ownerState rfl placePath ownerReplay
              (Nat.lt_of_lt_of_le bounded growth) ?_
            rw [countPrefix address.1 bounded]
            exact (ownerValue ownerLive).2
          · subst value
            have row := tables.occurrence_native_expression_row countNative
              (generated.lowerPlace owner (env := le) rfl) countTyped (rfl : lowerExpr count le address.2 = amount) live
            rw [row] at reference
            cases reference)
      intro value member _
      have alternatives : value = address.1 ∨ value = amount.1 := by
        simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Effect.uses] using member
      rcases alternatives with same | same
      · subst value
        have ownerLive := (dead_lowerExpr count).live_before rfl live
        have bounded : address.1 < middle.vals.size := ownerReady.roots.valueSize ▸ (ownerValue ownerLive).1
        apply OperandOccurrence.place placePath ownerReplay (Nat.lt_of_lt_of_le bounded growth)
        rw [countPrefix address.1 bounded]
        exact (ownerValue ownerLive).2
      · subst value
        exact OperandOccurrence.expression countPath countReplay
          (countReady.roots.valueSize ▸ (countValue live).bound) (countValue live).refined)
  have ledger := ((ownerLedger.retained growth countPrefix).underRoot placePath).trans
    ((countLedger.underRoot countPath).trans step)
  have finalSites := countSites.mutationEffect (effect := .popN address.1 amount.1 (some origin)) trivial (rfl : emitEffect (.popN address.1 amount.1 (some origin)) le amount.2 = _)
    (Nat.le_refl _) (fun _ _ => rfl)
  exact ⟨next, completed, retained, fun expected => occurrence_mutation_transfer loop typed rfl ready retained, ledger, finalSites⟩

theorem statementOccurrence_resizeWithoutFill {owner : Place} {count : Expr} (origin : OriginId) (loop : Option LoopCtx) (scope : ScopeId)
    (tables : SourceRootTables typingEnv env) (closed : ParameterRootsClosed func)
    (ownerChild : GlobalPlaceOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets owner initial upper)
    (countChild : ∀ provenance, GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets count
      (lowerPlace owner (lowerEnv env.mod env.impl.vars returnTypes) initial).2 provenance) :
    GlobalStatementOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets loop scope (.resize owner count none origin) initial upper := by
  intro occurrence output start finish before after typed replay ceiling _sourceScopes _stack ready sites targets generated _loopTargets _loopReplay _counterTyped _included native metadata continuation
  obtain ⟨path, globalPath⟩ := occurrence
  obtain ⟨info, element, integer, childStart, countFinish, ownerTyped, _elementType, countTyped, finishEq, _writable, _⟩ := tyStmt_resize_children typed
  subst countFinish
  obtain ⟨ownerRoots, ownerState, ownerReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  obtain ⟨countRoots, countState, countReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp tail
  have sourceReplay := replay
  rw [rpStmt_resize_noFill_eq_popN] at sourceReplay
  have sourceEffect := rpStmt_popN_effect ownerReplay countReplay sourceReplay
  have countCeiling : EffectRefinement func countState.eff target := by
    apply (mutation_read_shrink_aborts_extension _ _ ownerRoots).trans
    simpa only [sourceEffect] using ceiling
  have ownerCeiling := effectRefinement_before_expression countReplay countCeiling
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let address := lowerPlace owner le initial
  let amount := lowerExpr count le address.2
  have countNative : NativeRows vt amount.2 := by
    apply native.of_prefix
    exact types_emitEffect (.resize address.1 amount.1 none (some origin)) le amount.2 _ _ rfl
  have countMetadata : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func amount.2 := by
    apply metadata.of_advance
    exact advB_emitEffect (.resize address.1 amount.1 none (some origin)) le amount.2 _ _ rfl
  have countContinuation : NativeBuilderContinuation func amount.2 := by
    apply continuation.of_advance
    exact advB_emitEffect (.resize address.1 amount.1 none (some origin)) le amount.2 _ _ rfl
  have ownerNative := countNative.of_prefix (types_lowerExpr count le address.2 _ _ rfl)
  have ownerMetadata := countMetadata.of_advance (advB_lowerExpr count le address.2 _ _ rfl)
  have ownerContinuation := countContinuation.of_advance (advB_lowerExpr count le address.2 _ _ rfl)
  obtain ⟨middle, ownerReady, ownerValue, ownerPrefix, ownerLedger, ownerSites⟩ :=
    ownerChild ⟨path ++ [0], globalPath.snoc 0 rfl⟩ info start childStart before ownerState ownerRoots ownerTyped ownerReplay ownerCeiling ready sites targets generated ownerNative ownerMetadata ownerContinuation
  obtain ⟨next, countReady, countValue, countPrefix, countLedger, countSites⟩ :=
    countChild middle ⟨path ++ [1], globalPath.snoc 1 rfl⟩ (.int integer) childStart finish ownerState countState countRoots countTyped countReplay countCeiling
      ownerReady ownerSites (targets.mono (advB_lowerPlace owner le initial _ _ rfl).ext) (generated.lowerPlace owner rfl) countNative countMetadata countContinuation
  have completed := countReady.resizeWithoutFill loop ownerReplay countReplay replay ceiling rfl rfl
    closed
    (tables.mutation_origin_bound typed) (by
      intro live
      have ownerLive := (dead_lowerExpr count).live_before rfl live
      have oldBound := (ownerValue ownerLive).1
      have addressBound := Nat.lt_of_lt_of_le oldBound (advB_lowerExpr count le address.2 _ _ rfl).vals
      refine ⟨addressBound, (countValue live).bound, ?_⟩
      rw [countPrefix address.1 (by rw [ownerReady.roots.valueSize]; exact oldBound)]
      exact (ownerValue ownerLive).2)
  have retained (old : Nat) (bound : old < upper.vals.size) : rootsAt next.vals old = rootsAt upper.vals old := by
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, ownerReady.roots.valueSize]
      exact (advB_lowerPlace owner le initial _ _ rfl).vals
    exact (countPrefix old (Nat.lt_of_lt_of_le bound growth)).trans (ownerPrefix old bound)
  have growth : middle.vals.size ≤ next.vals.size := by
    rw [ownerReady.roots.valueSize, countReady.roots.valueSize]
    exact (advB_lowerExpr count le address.2 _ _ rfl).vals
  have placePath : DemandNodeAt (.statement (.resize owner count none origin)) [0] (.place owner) := .child rfl (.here _)
  have countPath : DemandNodeAt (.statement (.resize owner count none origin)) [1] (.expression count) := .child rfl (.here _)
  have step := occurrence_emitEffect_live (env := env) (root := .statement (.resize owner count none origin))
    (func := func) (types := vt) (upper := next)
    (rfl : emitEffect (.resize address.1 amount.1 none (some origin)) le amount.2 = _) (by
      intro live
      apply InstructionOccurrences.effect (ordinary := by intro address value origin same; cases same)
        (consumed := by
          intro value member mutability payload reference
          have alternatives : value = address.1 ∨ value = amount.1 := by
            simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Effect.uses] using member
          rcases alternatives with same | same
          · subst value
            have ownerLive := (dead_lowerExpr count).live_before rfl live
            have bounded : address.1 < middle.vals.size := ownerReady.roots.valueSize ▸ (ownerValue ownerLive).1
            refine .place address.1 env [0] owner before ownerRoots ownerState rfl placePath ownerReplay
              (Nat.lt_of_lt_of_le bounded growth) ?_
            rw [countPrefix address.1 bounded]
            exact (ownerValue ownerLive).2
          · subst value
            have row := tables.occurrence_native_expression_row countNative
              (generated.lowerPlace owner (env := le) rfl) countTyped (rfl : lowerExpr count le address.2 = amount) live
            rw [row] at reference
            cases reference)
      intro value member _
      have alternatives : value = address.1 ∨ value = amount.1 := by
        simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Effect.uses] using member
      rcases alternatives with same | same
      · subst value
        have ownerLive := (dead_lowerExpr count).live_before rfl live
        have bounded : address.1 < middle.vals.size := ownerReady.roots.valueSize ▸ (ownerValue ownerLive).1
        apply OperandOccurrence.place placePath ownerReplay (Nat.lt_of_lt_of_le bounded growth)
        rw [countPrefix address.1 bounded]
        exact (ownerValue ownerLive).2
      · subst value
        exact OperandOccurrence.expression countPath countReplay
          (countReady.roots.valueSize ▸ (countValue live).bound) (countValue live).refined)
  have ledger := ((ownerLedger.retained growth countPrefix).underRoot placePath).trans
    ((countLedger.underRoot countPath).trans step)
  have finalSites := countSites.mutationEffect (effect := .resize address.1 amount.1 none (some origin)) trivial (rfl : emitEffect (.resize address.1 amount.1 none (some origin)) le amount.2 = _)
    (Nat.le_refl _) (fun _ _ => rfl)
  exact ⟨next, completed, retained, fun expected => occurrence_mutation_transfer loop typed rfl ready retained, ledger, finalSites⟩

end Goose.Lower.Validation.ReplacementContentFlowSource
