import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceMutationsActions
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceMutationsCommon

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation ReplacementContentFlowSource

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {siteRoot : DemandNode} {siteTargets : List BlockId}
  {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}

theorem canonical_statementOccurrence_clear {ownerRoot : Fragment} {ownerInitial baseline : LS} {owner : Place} (origin : OriginId) (loop : Option LoopCtx) (scope : ScopeId)
    (tables : SourceRootTables typingEnv env) (closed : ParameterRootsClosed func)
    (child : CanonicalGlobalPlaceOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets owner initial upper) :
    CanonicalGlobalStatementOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets loop scope (.clear owner origin) initial upper := by
  intro occurrence cursor output start finish before after typed replay ceiling _sourceScopes _stack ready sites targets generated _loopTargets _loopReplay _counterTyped _included native metadata continuation
  obtain ⟨path, globalPath⟩ := occurrence
  obtain ⟨actualPath,located⟩ := cursor
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
    child ⟨path ++ [0], globalPath.snoc 0 rfl⟩ ⟨actualPath ++ [0],located.child rfl⟩ info start finish before ownerState ownerRoots ownerTyped ownerReplay ownerCeiling ready sites targets generated ownerNative ownerMetadata ownerContinuation
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

end Goose.Lower.Validation.SourceReplacementWriterLedger
