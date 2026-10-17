import Goose.Lower.Validation.SummaryPreservationSourceMutationKernelsCommon

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem fill_extension (func : Func) (source : Core.Eff) (roots : List RootRef) :
    EffectRefinement func source {source with
      reads := addTargets source.reads (rootsTargets roots)
      writes := addTargets source.writes (rootsTargets roots)
      grows := addTargets source.grows (rootsTargets roots)
      shrinks := addTargets source.shrinks (rootsTargets roots)
      aborts := true} := by
  refine ⟨?_, ?_, ?_, ?_, fun _ h => h, fun _ => rfl, fun h => h, fun h => h⟩
  all_goals exact storageTargets_mono (fun target member => addTargets_left _ _ target member)

theorem statementReplay_resizeWithFill {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}
    {owner : Place} {size fill : Expr} (origin : OriginId) (loop : Option LoopCtx) (scope : ScopeId)
    {context : ContextId} (tables : SourceRootTables typingEnv env)
    (accepted : Core.validate env.mod = .ok ())
    (contextRow : env.mod.contexts[context]? = some env.ctx)
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (ownerChild : PlaceReplayAt typingEnv env results vt target scopeCount owner initial upper)
    (sizeChild : ∀ provenance, ExpressionReplayAt typingEnv env results vt target scopeCount size
      (lowerPlace owner (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 provenance)
    (fillChild : ∀ provenance, ExpressionReplayAt typingEnv env results vt target scopeCount fill
      (lowerExpr size (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerPlace owner (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2).2 provenance) :
    StatementReplayAt typingEnv env results vt target scopeCount loop scope (.resize owner size (some fill) origin) initial upper := by
  intro output start finish before after typed replay ceiling _sourceScopes _stack ready generated _loopTargets native
  obtain ⟨info, element, integer, childStart, sizeFinish, ownerTyped, _elementType, sizeTyped, fillTyped, _writable, _⟩ :=
    tyStmt_resize_children typed
  obtain ⟨ownerRoots, ownerState, ownerReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  obtain ⟨sizeRoots, sizeState, sizeReplay, tail⟩ := (st_bind_ok _ _ _ _).mp tail
  obtain ⟨fillRoots, fillState, fillReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp tail
  have sourceEffect := rpStmt_resize_fill_effect ownerReplay sizeReplay fillReplay replay
  have fillCeiling : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) fillState.eff target := by
    apply (fill_extension _ _ ownerRoots).trans
    simpa only [sourceEffect] using ceiling
  have sizeCeiling := effectRefinement_before_expression fillReplay fillCeiling
  have ownerCeiling := effectRefinement_before_expression sizeReplay sizeCeiling
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let address := lowerPlace owner le initial
  let amount := lowerExpr size le address.2
  let value := lowerExpr fill le amount.2
  have fillNative : NativeRows vt value.2 := native.of_prefix
    (types_emitEffect (.resize address.1 amount.1 (some value.1) (some origin)) le value.2 _ _ rfl)
  have sizeNative := fillNative.of_prefix (types_lowerExpr fill le amount.2 _ _ rfl)
  have ownerNative := sizeNative.of_prefix (types_lowerExpr size le address.2 _ _ rfl)
  obtain ⟨ownerUpper, ownerReady, ownerValue, ownerPrefix⟩ :=
    ownerChild info start childStart before ownerState ownerRoots ownerTyped ownerReplay ownerCeiling ready generated ownerNative
  have ownerGenerated := generated.lowerPlace owner (env := le) rfl
  obtain ⟨sizeUpper, sizeReady, sizeValue, sizePrefix⟩ :=
    sizeChild ownerUpper (.int integer) childStart sizeFinish ownerState sizeState sizeRoots sizeTyped sizeReplay sizeCeiling
      ownerReady ownerGenerated sizeNative
  obtain ⟨next, fillReady, fillValue, fillPrefix⟩ :=
    fillChild sizeUpper element sizeFinish finish sizeState fillState fillRoots fillTyped fillReplay fillCeiling
      sizeReady (ownerGenerated.lowerExpr size rfl) fillNative
  have sizeGrowth := advB_lowerExpr size le address.2 amount.1 amount.2 rfl
  have fillGrowth := advB_lowerExpr fill le amount.2 value.1 value.2 rfl
  have completed := fillReady.resizeWithFill loop ownerReplay sizeReplay fillReplay replay ceiling rfl rfl rfl
    (lowerContextAt_parameterRoots_closed accepted contextRow implementationRow)
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
  exact ⟨next, completed, retained, mutation_statement_transfer loop typed rfl ready retained⟩

end Goose.Lower.Validation.SummaryPreservation
