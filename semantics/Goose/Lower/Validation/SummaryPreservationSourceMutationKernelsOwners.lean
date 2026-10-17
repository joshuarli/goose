import Goose.Lower.Validation.SummaryPreservationSourceMutationKernelsCommon

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}

theorem statementReplay_clear {owner : Place} (origin : OriginId) (loop : Option LoopCtx) (scope : ScopeId)
    {context : ContextId} (tables : SourceRootTables typingEnv env)
    (accepted : Core.validate env.mod = .ok ())
    (contextRow : env.mod.contexts[context]? = some env.ctx)
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (child : PlaceReplayAt typingEnv env results vt target scopeCount owner initial upper) :
    StatementReplayAt typingEnv env results vt target scopeCount loop scope (.clear owner origin) initial upper := by
  intro output start finish before after typed replay ceiling _sourceScopes _stack ready generated _loopTargets _loopReplay native
  obtain ⟨info, element, ownerTyped, _elementType, _writable, _⟩ := tyStmt_clear_children typed
  obtain ⟨ownerRoots, ownerState, ownerReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp replay
  have sourceEffect := rpStmt_clear_effect ownerReplay replay
  have ownerCeiling : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) ownerState.eff target := by
    apply (effectRefinement_read_shrink_extension _ _ ownerRoots).trans
    simpa only [sourceEffect] using ceiling
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let operand := lowerPlace owner le initial
  have ownerNative : NativeRows vt operand.2 := native.of_prefix (types_emitEffect (.clear operand.1 (some origin)) le operand.2 _ _ rfl)
  obtain ⟨next, ownerReady, ownerValue, retained⟩ :=
    child info start finish before ownerState ownerRoots ownerTyped ownerReplay ownerCeiling ready generated ownerNative
  have completed := ownerReady.clear loop ownerReplay replay ceiling rfl
    (lowerContextAt_parameterRoots_closed accepted contextRow implementationRow)
    (tables.mutation_origin_bound typed) ownerValue
  exact ⟨next, completed, retained, mutation_statement_transfer loop typed rfl ready retained⟩

theorem expressionReplay_pop {owner : Place} (origin : OriginId)
    {context : ContextId} (tables : SourceRootTables typingEnv env)
    (accepted : Core.validate env.mod = .ok ())
    (contextRow : env.mod.contexts[context]? = some env.ctx)
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (child : PlaceReplayAt typingEnv env results vt target scopeCount owner initial upper) :
    ExpressionReplayAt typingEnv env results vt target scopeCount (.pop owner origin) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  obtain ⟨info, ownerStart, ownerFinish, ownerTyped, _elementType⟩ := tyExpr_pop_owner typed
  obtain ⟨ownerRoots, ownerState, ownerReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp replay
  have sourceReplay := replay
  rw [rpExpr_pop_after_owner ownerReplay] at sourceReplay
  have afterEffect : after.eff = {ownerState.eff with
      reads := addTargets ownerState.eff.reads (rootsTargets ownerRoots)
      shrinks := addTargets ownerState.eff.shrinks (rootsTargets ownerRoots)
      aborts := true} := congrArg (fun result => result.2.eff) (Except.ok.inj sourceReplay).symm
  have ownerCeiling : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) ownerState.eff target := by
    apply (mutation_read_shrink_aborts_extension _ _ ownerRoots).trans
    simpa only [afterEffect] using ceiling
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let operand := lowerPlace owner le initial
  have ownerNative : NativeRows vt operand.2 := native.of_prefix (types_emitDef (.pop operand.1 (some origin)) le operand.2 _ _ rfl)
  obtain ⟨middle, ownerReady, ownerValue, ownerPrefix⟩ :=
    child info ownerStart ownerFinish before ownerState ownerRoots ownerTyped ownerReplay ownerCeiling ready generated ownerNative
  obtain ⟨next, completed, returned, retained⟩ := ownerReady.pop (type := type) ownerReplay replay ceiling rfl
    (lowerContextAt_parameterRoots_closed accepted contextRow implementationRow)
    (by simpa only [le, lowerEnv, tables.moduleEq] using Core.tyExpr_pop_success_origin_bound typed) ownerValue
  refine ⟨next, completed, returned, ?_⟩
  intro old bound
  have growth : upper.vals.size ≤ middle.vals.size := by
    rw [ready.roots.valueSize, ownerReady.roots.valueSize]
    exact (advB_lowerPlace owner le initial _ _ rfl).vals
  exact (retained old (Nat.lt_of_lt_of_le bound growth)).trans (ownerPrefix old bound)

end Goose.Lower.Validation.SummaryPreservation
