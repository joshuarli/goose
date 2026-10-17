import Goose.Lower.Validation.SummaryPreservationSourceMutationKernelsWholeCheckpoint

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

 theorem statementReplay_assignWhole {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}
    {owner : Place} {expression : Expr} (origin : OriginId) (loop : Option LoopCtx) (scope : ScopeId)
    {context : ContextId} (tables : SourceRootTables typingEnv env)
    (accepted : Core.validate env.mod = .ok ())
    (contextRow : env.mod.contexts[context]? = some env.ctx)
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (ownerChild : PlaceReplayAt typingEnv env results vt target scopeCount owner initial upper)
    (valueChild : ∀ provenance, ExpressionReplayAt typingEnv env results vt target scopeCount expression
      (Goose.Lower.emitEffect (.clear (lowerPlace owner (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 (some origin))
        (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerPlace owner (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2).2 provenance) :
    StatementReplayAt typingEnv env results vt target scopeCount loop scope (.assignWhole owner expression origin) initial upper := by
  intro output start finish before after typed replay ceiling _sourceScopes _stack ready generated _loopTargets native
  obtain ⟨info, element, childStart, ownerTyped, _ownerType, valueTyped, _binding, _contents, _⟩ := tyStmt_assignWhole_children typed
  obtain ⟨ownerRoots, ownerState, ownerReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp replay
  obtain ⟨valueRoots, valueState, valueReplay, sourceEffect⟩ := rpStmt_assignWhole_children ownerReplay replay
  have valueCeiling : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) valueState.eff target := by
    apply EffectRefinement.trans (middle := after.eff) ?_ ceiling
    rw [sourceEffect]
    refine ⟨fun _ h => h, ?_, ?_, fun _ h => h, fun _ h => h, fun h => h, fun h => h, fun h => h⟩
    all_goals exact storageTargets_mono (fun t h => addTargets_left _ _ t h)
  have clearCeiling := effectRefinement_before_expression valueReplay valueCeiling
  have ownerCeiling := (effectRefinement_read_shrink_extension _ _ ownerRoots).trans clearCeiling
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let address := lowerPlace owner le initial
  let cleared := Goose.Lower.emitEffect (.clear address.1 (some origin)) le address.2
  let value := lowerExpr expression le cleared.2
  have valueNative : NativeRows vt value.2 := native.of_prefix
    (types_emitEffect (.replace address.1 value.1 (some origin)) le value.2 _ _ rfl)
  have clearNative := valueNative.of_prefix (types_lowerExpr expression le cleared.2 _ _ rfl)
  have ownerNative := clearNative.of_prefix (types_emitEffect (.clear address.1 (some origin)) le address.2 _ _ rfl)
  obtain ⟨middle, ownerReady, ownerValue, ownerPrefix⟩ := ownerChild info start childStart before ownerState ownerRoots
    ownerTyped ownerReplay ownerCeiling ready generated ownerNative
  obtain ⟨next, completed, valuePrefix⟩ := ownerReady.assignWhole_checkpoint loop ownerReplay replay ceiling rfl
    (lowerContextAt_parameterRoots_closed accepted contextRow implementationRow) (tables.mutation_origin_bound typed)
    ownerValue (by
      intro childRoots childState provenance childReady childReplay
      rw [valueReplay] at childReplay
      cases childReplay
      obtain ⟨next, nextReady, childValue, childPrefix⟩ := valueChild provenance info.ty childStart finish
        _ valueState valueRoots valueTyped valueReplay valueCeiling childReady
        ((generated.lowerPlace owner rfl).emitEffect (.clear address.1 (some origin)) rfl) valueNative
      exact ⟨next, nextReady, fun live => (childValue live).bound, childPrefix⟩)
  have retained (old : Nat) (bound : old < upper.vals.size) : rootsAt next.vals old = rootsAt upper.vals old := by
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, ownerReady.roots.valueSize]
      exact (advB_lowerPlace owner le initial _ _ rfl).vals
    exact (valuePrefix old (Nat.lt_of_lt_of_le bound growth)).trans (ownerPrefix old bound)
  exact ⟨next, completed, retained, mutation_statement_transfer loop typed rfl ready retained⟩

end Goose.Lower.Validation.SummaryPreservation
