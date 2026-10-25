import Goose.Lower.Validation.SourceGlobalControlMutationsCommon
import Goose.Lower.Validation.SummaryPreservationSourceMutationKernelsWholeCheckpoint

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem globalStatementReplay_assignWhole {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}
    {owner : Place} {expression : Expr} (origin : OriginId) (loop : Option LoopCtx) (scope : ScopeId)
    (tables : SourceRootTables typingEnv env)
    (closed : ParameterRootsClosed func)
    (ownerChild : GlobalPlaceReplayAt typingEnv env results vt func returnTypes slots target scopeCount owner initial upper)
    (valueChild : ∀ provenance, GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount expression
      (Goose.Lower.emitEffect (.clear (lowerPlace owner (lowerEnv env.mod env.impl.vars returnTypes) initial).1 (some origin))
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerPlace owner (lowerEnv env.mod env.impl.vars returnTypes) initial).2).2 provenance) :
    GlobalStatementReplayAt typingEnv env results vt func returnTypes slots target scopeCount loop scope (.assignWhole owner expression origin) initial upper := by
  intro output start finish before after typed replay ceiling _sourceScopes _stack ready generated _loopTargets _loopReplay native
  obtain ⟨info, element, childStart, ownerTyped, _ownerType, valueTyped, _binding, _contents, _⟩ := tyStmt_assignWhole_children typed
  obtain ⟨ownerRoots, ownerState, ownerReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp replay
  obtain ⟨valueRoots, valueState, valueReplay, sourceEffect⟩ := rpStmt_assignWhole_children ownerReplay replay
  have valueCeiling : EffectRefinement func valueState.eff target := by
    apply EffectRefinement.trans (middle := after.eff) ?_ ceiling
    rw [sourceEffect]
    refine ⟨fun _ h => h, ?_, ?_, fun _ h => h, fun _ h => h, fun h => h, fun h => h, fun h => h⟩
    all_goals exact storageTargets_mono (fun t h => addTargets_left _ _ t h)
  have clearCeiling := effectRefinement_before_expression valueReplay valueCeiling
  have ownerCeiling := (effectRefinement_read_shrink_extension _ _ ownerRoots).trans clearCeiling
  let le := lowerEnv env.mod env.impl.vars returnTypes
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
    closed (tables.mutation_origin_bound typed)
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
  exact ⟨next, completed, retained, fun expected => global_statement_plain_transfer expected loop typed rfl ready retained⟩

end Goose.Lower.Validation.SummaryPreservation
