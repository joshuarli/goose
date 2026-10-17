import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceMutationsActions
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceMutationsCommon

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {siteRoot : DemandNode} {siteTargets : List BlockId}
  {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}

theorem statementOccurrence_clear {owner : Place} (origin : OriginId) (loop : Option LoopCtx) (scope : ScopeId)
    (tables : SourceRootTables typingEnv env) (closed : ParameterRootsClosed func)
    (child : GlobalPlaceOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets owner initial upper) :
    GlobalStatementOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets loop scope (.clear owner origin) initial upper := by
  intro occurrence output start finish before after typed replay ceiling _sourceScopes _stack ready sites targets generated _loopTargets _loopReplay _counterTyped _included native metadata continuation
  obtain ⟨path, globalPath⟩ := occurrence
  obtain ⟨info, element, ownerTyped, _elementType, _writable, _⟩ := tyStmt_clear_children typed
  obtain ⟨ownerRoots, ownerState, ownerReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp replay
  have sourceEffect := rpStmt_clear_effect ownerReplay replay
  have ownerCeiling : EffectRefinement func ownerState.eff target := by
    apply (effectRefinement_read_shrink_extension _ _ ownerRoots).trans
    simpa only [sourceEffect] using ceiling
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let operand := lowerPlace owner le initial
  have ownerNative : NativeRows vt operand.2 := native.of_prefix (types_emitEffect (.clear operand.1 (some origin)) le operand.2 _ _ rfl)
  have ownerMetadata := metadata.of_advance (advB_emitEffect (.clear operand.1 (some origin)) le operand.2 _ _ rfl)
  have ownerContinuation := continuation.of_advance (advB_emitEffect (.clear operand.1 (some origin)) le operand.2 _ _ rfl)
  obtain ⟨next, ownerReady, ownerValue, retained, ownerLedger, ownerSites⟩ :=
    child ⟨path ++ [0], globalPath.snoc 0 rfl⟩ info start finish before ownerState ownerRoots ownerTyped ownerReplay ownerCeiling ready sites targets generated ownerNative ownerMetadata ownerContinuation
  have completed := ownerReady.clear loop ownerReplay replay ceiling rfl
    closed
    (tables.mutation_origin_bound typed) ownerValue
  have childPath : DemandNodeAt (.statement (.clear owner origin)) [0] (.place owner) := .child rfl (.here _)
  have step := occurrence_emitEffect_live (env := env) (root := .statement (.clear owner origin))
    (func := func) (types := vt) (upper := next)
    (rfl : emitEffect (.clear operand.1 (some origin)) le operand.2 = _)
    (by
      intro live
      apply InstructionOccurrences.effect (ordinary := by intro address value origin same; cases same)
        (consumed := by
          intro value member _ _ _
          have same : value = operand.1 := by simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Effect.uses] using member
          subst value
          exact .place operand.1 env [0] owner before ownerRoots ownerState rfl childPath ownerReplay
            (ownerReady.roots.valueSize ▸ (ownerValue live).1) (ownerValue live).2)
      intro value member _
      have same : value = operand.1 := by simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Effect.uses] using member
      subst value
      exact OperandOccurrence.place childPath ownerReplay
        (ownerReady.roots.valueSize ▸ (ownerValue live).1) (ownerValue live).2)
  have ledger := (ownerLedger.underRoot childPath).trans step
  have finalSites := ownerSites.mutationEffect (effect := .clear operand.1 (some origin)) trivial (rfl : emitEffect (.clear operand.1 (some origin)) le operand.2 = _)
    (Nat.le_refl _) (fun _ _ => rfl)
  exact ⟨next, completed, retained, fun expected => occurrence_mutation_transfer loop typed rfl ready retained, ledger, finalSites⟩

theorem expressionOccurrence_pop {owner : Place} (origin : OriginId)
    (tables : SourceRootTables typingEnv env) (closed : ParameterRootsClosed func)
    (child : GlobalPlaceOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets owner initial upper) :
    GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets (.pop owner origin) initial upper := by
  intro occurrence type start finish before after roots typed replay ceiling ready sites targets generated native metadata continuation
  obtain ⟨path, globalPath⟩ := occurrence
  obtain ⟨info, ownerStart, ownerFinish, ownerTyped, _elementType⟩ := tyExpr_pop_owner typed
  obtain ⟨ownerRoots, ownerState, ownerReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp replay
  have sourceReplay := replay
  rw [rpExpr_pop_after_owner ownerReplay] at sourceReplay
  have afterEffect : after.eff = {ownerState.eff with
      reads := addTargets ownerState.eff.reads (rootsTargets ownerRoots)
      shrinks := addTargets ownerState.eff.shrinks (rootsTargets ownerRoots)
      aborts := true} := congrArg (fun result => result.2.eff) (Except.ok.inj sourceReplay).symm
  have ownerCeiling : EffectRefinement func ownerState.eff target := by
    apply (mutation_read_shrink_aborts_extension _ _ ownerRoots).trans
    simpa only [afterEffect] using ceiling
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let operand := lowerPlace owner le initial
  have ownerNative : NativeRows vt operand.2 := native.of_prefix (types_emitDef (.pop operand.1 (some origin)) le operand.2 _ _ rfl)
  have ownerMetadata := metadata.of_advance (advB_emitDef (.pop operand.1 (some origin)) le operand.2 _ _ rfl)
  have ownerContinuation := continuation.of_advance (advB_emitDef (.pop operand.1 (some origin)) le operand.2 _ _ rfl)
  obtain ⟨middle, ownerReady, ownerValue, ownerPrefix, ownerLedger, ownerSites⟩ :=
    child ⟨path ++ [0], globalPath.snoc 0 rfl⟩ info ownerStart ownerFinish before ownerState ownerRoots ownerTyped ownerReplay ownerCeiling ready sites targets generated ownerNative ownerMetadata ownerContinuation
  obtain ⟨next, completed, returned, retained⟩ := ownerReady.pop (type := type) ownerReplay replay ceiling rfl
    closed
    (by simpa only [le, lowerEnv, tables.moduleEq] using Core.tyExpr_pop_success_origin_bound typed) ownerValue
  have initialPrefix : ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old := by
    intro old bound
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, ownerReady.roots.valueSize]
      exact (advB_lowerPlace owner le initial _ _ rfl).vals
    exact (retained old (Nat.lt_of_lt_of_le bound growth)).trans (ownerPrefix old bound)
  have growth : middle.vals.size ≤ next.vals.size := by
    rw [ownerReady.roots.valueSize, completed.roots.valueSize]
    exact (advB_emitDef (.pop operand.1 (some origin)) le operand.2 _ _ rfl).vals
  have childPath : DemandNodeAt (.expression (.pop owner origin)) [0] (.place owner) := .child rfl (.here _)
  have step := occurrence_emitDef_live (env := env) (root := .expression (.pop owner origin))
    (func := func) (types := vt) (upper := next)
    (rfl : emitDef (.pop operand.1 (some origin)) le operand.2 = _)
    (by
      intro live
      apply InstructionOccurrences.definition
      · intro value member _
        have same : value = operand.1 := by simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] using member
        subst value
        have oldBound : operand.1 < middle.vals.size := ownerReady.roots.valueSize ▸ (ownerValue live).1
        apply OperandOccurrence.place childPath ownerReplay (Nat.lt_of_lt_of_le oldBound growth)
        rw [retained operand.1 oldBound]
        exact (ownerValue live).2
      · intro address same; cases same
      · intro fn args origin same; cases same
      · intro value member _ _ _
        have same : value = operand.1 := by simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] using member
        subst value
        have oldBound : operand.1 < middle.vals.size := ownerReady.roots.valueSize ▸ (ownerValue live).1
        refine .place operand.1 env [0] owner before ownerRoots ownerState rfl childPath ownerReplay
          (Nat.lt_of_lt_of_le oldBound growth) ?_
        rw [retained operand.1 oldBound]
        exact (ownerValue live).2)
  have ledger := ((ownerLedger.retained growth retained).underRoot childPath).trans step
  have finalSites := ownerSites.emitDef (rfl : emitDef (.pop operand.1 (some origin)) le operand.2 = _) growth retained
  exact ⟨next, completed, returned, initialPrefix, ledger, finalSites⟩

end Goose.Lower.Validation.ReplacementContentFlowSource
