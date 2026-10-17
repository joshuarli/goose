import Goose.Lower.Validation.SourceGlobalControlMutationsCommon
import Goose.Lower.Validation.SummaryPreservationSourceMutationKernelsAssignShape
import Goose.Lower.Validation.SummaryPreservationReplayRefSlicePlace

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem globalStatementReplay_assign {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}
    {place : Place} {expression : Expr} (origin : OriginId) (loop : Option LoopCtx) (scope : ScopeId)
    (tables : SourceRootTables typingEnv env)
    (variables : typingEnv.vars = #[]) (closed : ParameterRootsClosed func)
    (placeChild : GlobalPlaceReplayAt typingEnv env results vt func returnTypes slots target scopeCount place initial upper)
    (valueChild : ∀ provenance, GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount expression
      (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).2 provenance) :
    GlobalStatementReplayAt typingEnv env results vt func returnTypes slots target scopeCount loop scope (.assign place expression origin) initial upper := by
  intro output start finish before after typed replay ceiling _sourceScopes _stack ready generated _loopTargets _loopReplay native
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
  have placeNative := valueNative.of_prefix (types_lowerExpr expression le address.2 _ _ rfl)
  have classified := mutation_assign_source_cases tables placeTyped shape
  have nonref : info.ty.isRefLike = false := by
    rcases classified with nonref | ⟨parameter, localVar, _, row, _⟩
    · exact nonref
    · rw [tables.variablesEq, variables] at row
      simp at row
  obtain ⟨middle, placeReady, placeValue, placePrefix⟩ := placeChild info start childStart before placeState placeRoots
    placeTyped placeReplay placeCeiling ready generated placeNative
  obtain ⟨next, valueReady, valueFacts, valuePrefix⟩ := valueChild middle info.ty childStart finish placeState valueState valueRoots
    valueTyped valueReplay valueCeiling placeReady (generated.lowerPlace place rfl) valueNative
  have retained (old : Nat) (bound : old < upper.vals.size) : rootsAt next.vals old = rootsAt upper.vals old := by
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, placeReady.roots.valueSize]
      exact (advB_lowerPlace place le initial _ _ rfl).vals
    exact (valuePrefix old (Nat.lt_of_lt_of_le bound growth)).trans (placePrefix old bound)
  have completed : ReplayBuilder (lower env.mod) results vt func target le scopeCount
      slots (lowerStmt loop (.assign place expression origin) le initial).2 next := by
    apply valueReady.assignNonref loop placeReplay valueReplay replay ceiling rfl rfl
      closed (tables.mutation_origin_bound typed)
    intro live
    have placeLive := (dead_lowerExpr expression).live_before rfl live
    have placeBound := (placeValue placeLive).1
    refine ⟨Nat.lt_of_lt_of_le placeBound (advB_lowerExpr expression le address.2 _ _ rfl).vals,
      (valueFacts live).bound, ?_, ?_, (valueFacts live).scalar nonref⟩
    · rw [valuePrefix address.1 (by rw [placeReady.roots.valueSize]; exact placeBound)]
      exact (placeValue placeLive).2
    · rw [tables.global_native_place_owner placeNative generated placeTyped rfl placeLive]
      exact nonref
  exact ⟨next, completed, retained, fun expected => global_statement_plain_transfer expected loop typed rfl ready retained⟩

end Goose.Lower.Validation.SummaryPreservation
