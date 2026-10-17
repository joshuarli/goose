import Goose.Lower.Validation.SourceGlobalControlMutationsCommon

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}

theorem globalStatementReplay_clear {owner : Place} (origin : OriginId) (loop : Option LoopCtx) (scope : ScopeId)
    (tables : SourceRootTables typingEnv env)
    (closed : ParameterRootsClosed func)
    (child : GlobalPlaceReplayAt typingEnv env results vt func returnTypes slots target scopeCount owner initial upper) :
    GlobalStatementReplayAt typingEnv env results vt func returnTypes slots target scopeCount loop scope (.clear owner origin) initial upper := by
  intro output start finish before after typed replay ceiling _sourceScopes _stack ready generated _loopTargets _loopReplay native
  obtain ⟨info, element, ownerTyped, _elementType, _writable, _⟩ := tyStmt_clear_children typed
  obtain ⟨ownerRoots, ownerState, ownerReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp replay
  have sourceEffect := rpStmt_clear_effect ownerReplay replay
  have ownerCeiling : EffectRefinement func ownerState.eff target := by
    apply (effectRefinement_read_shrink_extension _ _ ownerRoots).trans
    simpa only [sourceEffect] using ceiling
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let operand := lowerPlace owner le initial
  have ownerNative : NativeRows vt operand.2 := native.of_prefix (types_emitEffect (.clear operand.1 (some origin)) le operand.2 _ _ rfl)
  obtain ⟨next, ownerReady, ownerValue, retained⟩ :=
    child info start finish before ownerState ownerRoots ownerTyped ownerReplay ownerCeiling ready generated ownerNative
  have completed := ownerReady.clear loop ownerReplay replay ceiling rfl
    closed
    (tables.mutation_origin_bound typed) ownerValue
  exact ⟨next, completed, retained, fun expected => global_statement_plain_transfer expected loop typed rfl ready retained⟩

end Goose.Lower.Validation.SummaryPreservation
