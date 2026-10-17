import Goose.Lower.Validation.SummaryPreservationSourceMutationKernelsAssignShape
import Goose.Lower.Validation.SummaryPreservationReplayRefSlicePlace

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

 theorem statementReplay_assign {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}
    {place : Place} {expression : Expr} (origin : OriginId) (loop : Option LoopCtx) (scope : ScopeId)
    {context : ContextId} (tables : SourceRootTables typingEnv env)
    (accepted : Core.validate env.mod = .ok ())
    (contextRow : env.mod.contexts[context]? = some env.ctx)
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (placeChild : PlaceReplayAt typingEnv env results vt target scopeCount place initial upper)
    (valueChild : ∀ provenance, ExpressionReplayAt typingEnv env results vt target scopeCount expression
      (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 provenance) :
    StatementReplayAt typingEnv env results vt target scopeCount loop scope (.assign place expression origin) initial upper := by
  intro output start finish before after typed replay ceiling _sourceScopes _stack ready generated _loopTargets _loopReplay native
  obtain ⟨info, childStart, placeTyped, valueTyped, shape, _writable, _⟩ := tyStmt_assign_children typed
  obtain ⟨placeRoots, placeState, placeReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  obtain ⟨valueRoots, valueState, valueReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp tail
  have sourceEffect := (rpStmt_assign_contract placeReplay valueReplay replay).2
  have valueCeiling : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) valueState.eff target := by
    apply EffectRefinement.trans (middle := after.eff) ?_ ceiling
    rw [sourceEffect]
    refine ⟨fun _ h => h, ?_, fun _ h => h, fun _ h => h, ?_, fun h => h, fun h => h, fun h => h⟩
    · exact storageTargets_mono (fun t h => addTargets_left _ _ t h)
    · exact fun t h => addTargets_left _ _ t h
  have placeCeiling := effectRefinement_before_expression valueReplay valueCeiling
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let address := lowerPlace place le initial
  let value := lowerExpr expression le address.2
  have valueNative : NativeRows vt value.2 := native.of_prefix
    (types_emitEffect (.store address.1 value.1 (some origin)) le value.2 _ _ rfl)
  have placeNative := valueNative.of_prefix (types_lowerExpr expression le address.2 _ _ rfl)
  have classified := mutation_assign_source_cases tables placeTyped shape
  have ownerPackage : ∃ middle,
      ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target le scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl) address.2 middle ∧
      (address.2.cur.isSome = true → address.1 < address.2.vals.size ∧
        RootsRefine (lowerContextAt env.mod env.ctx env.impl) (rootsAt middle.vals address.1) placeRoots) ∧
      (∀ old, old < upper.vals.size → rootsAt middle.vals old = rootsAt upper.vals old) ∧
      (info.ty.isRefLike = false ∨ ∃ parameter,
        place.derefVar? = some parameter ∧ env.isRefSliceVar parameter = true ∧ parameter < env.impl.params.size ∧
        (address.2.cur.isSome = true → ∀ root ∈ rootsAt middle.vals address.1, root ∈ [RootRef.param parameter])) := by
    rcases classified with nonref | ⟨parameter, localVar, placeEq, variableRow, reference⟩
    · obtain ⟨middle, placeReady, placeValue, placePrefix⟩ := placeChild info start childStart before placeState placeRoots
        placeTyped placeReplay placeCeiling ready generated placeNative
      exact ⟨middle, placeReady, placeValue, placePrefix, Or.inl nonref⟩
    · subst place
      obtain ⟨bound, refSlice, middle, placeReady, placeValue, placePrefix⟩ :=
        ready.referenceSlicePlace accepted contextRow implementationRow variableRow reference placeReplay
      exact ⟨middle, placeReady, fun live => ⟨(placeValue live).1, (placeValue live).2.1⟩,
        placePrefix, Or.inr ⟨parameter, rfl, refSlice, bound, fun live => (placeValue live).2.2⟩⟩
  obtain ⟨middle, placeReady, placeValue, placePrefix, storeCase⟩ := ownerPackage
  obtain ⟨next, valueReady, valueFacts, valuePrefix⟩ := valueChild middle info.ty childStart finish placeState valueState valueRoots
    valueTyped valueReplay valueCeiling placeReady (generated.lowerPlace place rfl) valueNative
  have retained (old : Nat) (bound : old < upper.vals.size) : rootsAt next.vals old = rootsAt upper.vals old := by
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, placeReady.roots.valueSize]
      exact (advB_lowerPlace place le initial _ _ rfl).vals
    exact (valuePrefix old (Nat.lt_of_lt_of_le bound growth)).trans (placePrefix old bound)
  have completed : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target le scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) (lowerStmt loop (.assign place expression origin) le initial).2 next := by
    rcases storeCase with nonref | ⟨parameter, deref, reference, parameterBound, identity⟩
    · apply valueReady.assignNonref loop placeReplay valueReplay replay ceiling rfl rfl
        (lowerContextAt_parameterRoots_closed accepted contextRow implementationRow) (tables.mutation_origin_bound typed)
      intro live
      have placeLive := (dead_lowerExpr expression).live_before rfl live
      have placeBound := (placeValue placeLive).1
      refine ⟨Nat.lt_of_lt_of_le placeBound (advB_lowerExpr expression le address.2 _ _ rfl).vals,
        (valueFacts live).bound, ?_, ?_, (valueFacts live).scalar nonref⟩
      · rw [valuePrefix address.1 (by rw [placeReady.roots.valueSize]; exact placeBound)]
        exact (placeValue placeLive).2
      · rw [tables.native_place_owner placeNative generated placeTyped rfl placeLive]
        exact nonref
    · apply valueReady.assignRefSlice loop placeReplay valueReplay replay ceiling rfl rfl
        (lowerContextAt_parameterRoots_closed accepted contextRow implementationRow) (tables.mutation_origin_bound typed)
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
  exact ⟨next, completed, retained, mutation_statement_transfer loop typed rfl ready retained⟩

end Goose.Lower.Validation.SummaryPreservation
