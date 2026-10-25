import Goose.Lower.Validation.SourceGlobalControlMutationsCommon

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}

theorem globalStatementReplay_popN {owner : Place} {count : Expr} (origin : OriginId) (loop : Option LoopCtx) (scope : ScopeId)
    (tables : SourceRootTables typingEnv env)
    (closed : ParameterRootsClosed func)
    (ownerChild : GlobalPlaceReplayAt typingEnv env results vt func returnTypes slots target scopeCount owner initial upper)
    (countChild : ∀ provenance, GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount count
      (lowerPlace owner (lowerEnv env.mod env.impl.vars returnTypes) initial).2 provenance) :
    GlobalStatementReplayAt typingEnv env results vt func returnTypes slots target scopeCount loop scope (.popN owner count origin) initial upper := by
  intro output start finish before after typed replay ceiling _sourceScopes _stack ready generated _loopTargets _loopReplay native
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
  have ownerNative := countNative.of_prefix (types_lowerExpr count le address.2 _ _ rfl)
  obtain ⟨middle, ownerReady, ownerValue, ownerPrefix⟩ :=
    ownerChild info start childStart before ownerState ownerRoots ownerTyped ownerReplay ownerCeiling ready generated ownerNative
  obtain ⟨next, countReady, countValue, countPrefix⟩ :=
    countChild middle (.int integer) childStart finish ownerState countState countRoots countTyped countReplay countCeiling
      ownerReady (generated.lowerPlace owner rfl) countNative
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
  exact ⟨next, completed, retained, fun expected => global_statement_plain_transfer expected loop typed rfl ready retained⟩

theorem globalStatementReplay_resizeWithoutFill {owner : Place} {count : Expr} (origin : OriginId) (loop : Option LoopCtx) (scope : ScopeId)
    (tables : SourceRootTables typingEnv env)
    (closed : ParameterRootsClosed func)
    (ownerChild : GlobalPlaceReplayAt typingEnv env results vt func returnTypes slots target scopeCount owner initial upper)
    (countChild : ∀ provenance, GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount count
      (lowerPlace owner (lowerEnv env.mod env.impl.vars returnTypes) initial).2 provenance) :
    GlobalStatementReplayAt typingEnv env results vt func returnTypes slots target scopeCount loop scope (.resize owner count none origin) initial upper := by
  intro output start finish before after typed replay ceiling _sourceScopes _stack ready generated _loopTargets _loopReplay native
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
  have ownerNative := countNative.of_prefix (types_lowerExpr count le address.2 _ _ rfl)
  obtain ⟨middle, ownerReady, ownerValue, ownerPrefix⟩ :=
    ownerChild info start childStart before ownerState ownerRoots ownerTyped ownerReplay ownerCeiling ready generated ownerNative
  obtain ⟨next, countReady, countValue, countPrefix⟩ :=
    countChild middle (.int integer) childStart finish ownerState countState countRoots countTyped countReplay countCeiling
      ownerReady (generated.lowerPlace owner rfl) countNative
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
  exact ⟨next, completed, retained, fun expected => global_statement_plain_transfer expected loop typed rfl ready retained⟩

end Goose.Lower.Validation.SummaryPreservation
