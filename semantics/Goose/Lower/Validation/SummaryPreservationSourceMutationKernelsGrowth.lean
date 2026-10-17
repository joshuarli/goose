import Goose.Lower.Validation.SummaryPreservationSourceMutationKernelsCommon

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem growth_extension (func : Func) (source : Core.Eff) (owners reads : List RootRef)
    (profile : ArtifactProfile) (limited : Bool) :
    EffectRefinement func source (if profile == .shrink then {source with
      reads := addTargets source.reads (rootsTargets reads)
      grows := addTargets source.grows (rootsTargets owners)
      writes := addTargets source.writes (rootsTargets owners)
      aborts := source.aborts || limited} else {source with
      reads := addTargets source.reads (rootsTargets reads)
      grows := addTargets source.grows (rootsTargets owners)}) := by
  cases profile
  · refine ⟨?_, fun _ h => h, ?_, fun _ h => h, fun _ h => h, fun h => h, fun h => h, fun h => h⟩
    all_goals exact storageTargets_mono (fun target member => addTargets_left _ _ target member)
  · refine ⟨?_, ?_, ?_, fun _ h => h, fun _ h => h, ?_, fun h => h, fun h => h⟩
    · exact storageTargets_mono (fun target member => addTargets_left _ _ target member)
    · exact storageTargets_mono (fun target member => addTargets_left _ _ target member)
    · exact storageTargets_mono (fun target member => addTargets_left _ _ target member)
    · intro h
      simp [h]

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}

theorem expressionReplay_push {owner : Place} {expression : Expr} (origin : Option OriginId)
    {context : ContextId} (tables : SourceRootTables typingEnv env)
    (accepted : Core.validate env.mod = .ok ())
    (contextRow : env.mod.contexts[context]? = some env.ctx)
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (ownerChild : PlaceReplayAt typingEnv env results vt target scopeCount owner initial upper)
    (valueChild : ∀ provenance, ExpressionReplayAt typingEnv env results vt target scopeCount expression
      (lowerPlace owner (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 provenance) :
    ExpressionReplayAt typingEnv env results vt target scopeCount (.push owner expression origin) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  obtain ⟨info, element, ownerStart, ownerFinish, childStart, childFinish, ownerTyped, _elementType, valueTyped, typeEq⟩ :=
    tyExpr_push_children typed
  subst type
  obtain ⟨ownerRoots, ownerState, ownerReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  obtain ⟨valueRoots, valueState, valueReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp tail
  have sourceType := tyPlace_accessType tables.moduleEq.symm tables.variablesEq.symm ownerTyped
  obtain ⟨limited, limitedRun⟩ : ∃ limited, env.limitedOwner owner = .ok limited := by
    cases shape : info.ty <;> simp only [PEnv.limitedOwner, sourceType, shape] <;> first | exact ⟨false, rfl⟩ | exact ⟨true, rfl⟩
  have sourceReplay := replay
  rw [rpExpr_push_after_operands ownerReplay valueReplay limitedRun] at sourceReplay
  have sourceEffect := congrArg (fun result => result.2.eff) (Except.ok.inj sourceReplay).symm
  have valueCeiling : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) valueState.eff target := by
    apply (growth_extension _ _ ownerRoots [] env.mod.profile limited).trans
    cases profile : env.mod.profile <;>
      simp [profile] at sourceEffect ⊢ <;> rw [sourceEffect] at ceiling <;>
      simpa [rootsTargets, addTargets] using ceiling
  have ownerCeiling := effectRefinement_before_expression valueReplay valueCeiling
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let address := lowerPlace owner le initial
  let value := lowerExpr expression le address.2
  have valueNative : NativeRows vt value.2 := native.of_prefix (types_emitDef (.push address.1 value.1 origin) le value.2 _ _ rfl)
  have ownerNative := valueNative.of_prefix (types_lowerExpr expression le address.2 _ _ rfl)
  obtain ⟨middle, ownerReady, ownerValue, ownerPrefix⟩ :=
    ownerChild info ownerStart ownerFinish before ownerState ownerRoots ownerTyped ownerReplay ownerCeiling ready generated ownerNative
  obtain ⟨valueUpper, valueReady, valueFacts, valuePrefix⟩ :=
    valueChild middle element childStart childFinish ownerState valueState valueRoots valueTyped valueReplay valueCeiling
      ownerReady (generated.lowerPlace owner rfl) valueNative
  obtain ⟨mutability, actualType⟩ : ∃ mutability, value.2.cur.isSome = true →
      vt[address.1]? = some (some (.data (.ref mutability info.ty))) := by
    by_cases live : value.2.cur.isSome = true
    · obtain ⟨mutability, row⟩ := tables.native_place_row ownerNative generated ownerTyped rfl
        ((dead_lowerExpr expression).live_before rfl live)
      exact ⟨mutability, fun _ => row⟩
    · exact ⟨.readOnly, fun active => (live active).elim⟩
  obtain ⟨next, completed, returned, retained⟩ := valueReady.push (element := element)
    ownerReplay valueReplay replay ceiling rfl rfl
    (lowerContextAt_parameterRoots_closed accepted contextRow implementationRow) rfl
    (by intro candidate selected; subst origin; simpa only [le, lowerEnv, tables.moduleEq] using Core.tyExpr_push_success_origin_bound typed)
    sourceType actualType (by
      intro live
      have ownerLive := (dead_lowerExpr expression).live_before rfl live
      have oldBound := (ownerValue ownerLive).1
      refine ⟨Nat.lt_of_lt_of_le oldBound (advB_lowerExpr expression le address.2 _ _ rfl).vals,
        (valueFacts live).bound, ?_⟩
      rw [valuePrefix address.1 (by rw [ownerReady.roots.valueSize]; exact oldBound)]
      exact (ownerValue ownerLive).2)
  refine ⟨next, completed, returned, ?_⟩
  intro old bound
  have ownerGrowth : upper.vals.size ≤ middle.vals.size := by
    rw [ready.roots.valueSize, ownerReady.roots.valueSize]
    exact (advB_lowerPlace owner le initial _ _ rfl).vals
  have valueGrowth : middle.vals.size ≤ valueUpper.vals.size := by
    rw [ownerReady.roots.valueSize, valueReady.roots.valueSize]
    exact (advB_lowerExpr expression le address.2 _ _ rfl).vals
  exact (retained old (Nat.lt_of_lt_of_le bound (Nat.le_trans ownerGrowth valueGrowth))).trans
    ((valuePrefix old (Nat.lt_of_lt_of_le bound ownerGrowth)).trans (ownerPrefix old bound))

theorem statementReplay_append {owner : Place} {view : View} (origin : OriginId) (loop : Option LoopCtx) (scope : ScopeId)
    {context : ContextId} (tables : SourceRootTables typingEnv env)
    (accepted : Core.validate env.mod = .ok ())
    (contextRow : env.mod.contexts[context]? = some env.ctx)
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (ownerChild : PlaceReplayAt typingEnv env results vt target scopeCount owner initial upper)
    (viewChild : ∀ provenance, ViewReplayAt typingEnv env results vt target scopeCount view
      (lowerPlace owner (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 provenance) :
    StatementReplayAt typingEnv env results vt target scopeCount loop scope (.append owner view origin) initial upper := by
  intro output start finish before after typed replay ceiling _sourceScopes _stack ready generated _loopTargets native
  obtain ⟨info, element, writable, childStart, ownerTyped, _elementType, viewTyped, _writable, _⟩ := tyStmt_append_children typed
  obtain ⟨ownerRoots, ownerState, ownerReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  obtain ⟨viewRoots, viewState, viewReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp tail
  have sourceType := tyPlace_accessType tables.moduleEq.symm tables.variablesEq.symm ownerTyped
  obtain ⟨limited, limitedRun⟩ : ∃ limited, env.limitedOwner owner = .ok limited := by
    cases shape : info.ty <;> simp only [PEnv.limitedOwner, sourceType, shape] <;> first | exact ⟨false, rfl⟩ | exact ⟨true, rfl⟩
  have sourceEffect := rpStmt_append_effect ownerReplay viewReplay limitedRun replay
  have viewCeiling : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) viewState.eff target := by
    apply (growth_extension _ _ ownerRoots viewRoots env.mod.profile limited).trans
    simpa only [sourceEffect] using ceiling
  have ownerCeiling := effectRefinement_before_of_replay (rp_mono_all.2.1 env view)
    (rp_rebinds_mono_all.2.1 env view) (rp_flags_mono_all.2.1 env view) viewReplay viewCeiling
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let address := lowerPlace owner le initial
  let value := lowerView view le address.2
  have viewNative : NativeRows vt value.2 := native.of_prefix (types_emitEffect (.append address.1 value.1 (some origin)) le value.2 _ _ rfl)
  have ownerNative := viewNative.of_prefix (types_lowerView view le address.2 _ _ rfl)
  obtain ⟨middle, ownerReady, ownerValue, ownerPrefix⟩ :=
    ownerChild info start childStart before ownerState ownerRoots ownerTyped ownerReplay ownerCeiling ready generated ownerNative
  obtain ⟨next, viewReady, viewValue, viewPrefix⟩ :=
    viewChild middle (element, writable) childStart finish ownerState viewState viewRoots viewTyped viewReplay viewCeiling
      ownerReady (generated.lowerPlace owner rfl) viewNative
  obtain ⟨mutability, actualType⟩ : ∃ mutability, value.2.cur.isSome = true →
      vt[address.1]? = some (some (.data (.ref mutability info.ty))) := by
    by_cases live : value.2.cur.isSome = true
    · obtain ⟨mutability, row⟩ := tables.native_place_row ownerNative generated ownerTyped rfl
        ((dead_lowerView view).live_before rfl live)
      exact ⟨mutability, fun _ => row⟩
    · exact ⟨.readOnly, fun active => (live active).elim⟩
  have completed := viewReady.append loop ownerReplay viewReplay replay ceiling rfl rfl
    (lowerContextAt_parameterRoots_closed accepted contextRow implementationRow) rfl
    (tables.mutation_origin_bound typed) sourceType actualType (by
      intro live
      have ownerLive := (dead_lowerView view).live_before rfl live
      have oldBound := (ownerValue ownerLive).1
      refine ⟨Nat.lt_of_lt_of_le oldBound (advB_lowerView view le address.2 _ _ rfl).vals,
        (viewValue live).bound, ?_, (viewValue live).refined⟩
      rw [viewPrefix address.1 (by rw [ownerReady.roots.valueSize]; exact oldBound)]
      exact (ownerValue ownerLive).2)
  have retained (old : Nat) (bound : old < upper.vals.size) : rootsAt next.vals old = rootsAt upper.vals old := by
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, ownerReady.roots.valueSize]
      exact (advB_lowerPlace owner le initial _ _ rfl).vals
    exact (viewPrefix old (Nat.lt_of_lt_of_le bound growth)).trans (ownerPrefix old bound)
  exact ⟨next, completed, retained, mutation_statement_transfer loop typed rfl ready retained⟩

end Goose.Lower.Validation.SummaryPreservation
