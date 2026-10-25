import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceMutationsActions
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceMutationsCommon

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation ReplacementContentFlowSource

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
  {siteRoot : DemandNode} {siteTargets : List BlockId}
  {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}

theorem canonical_statementOccurrence_append {ownerRoot : Fragment} {ownerInitial baseline : LS} {owner : Place} {view : View} (origin : OriginId) (loop : Option LoopCtx) (scope : ScopeId)
    (tables : SourceRootTables typingEnv env) (closed : ParameterRootsClosed func)
    (ownerChild : CanonicalGlobalPlaceOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets owner initial upper)
    (viewChild : ∀ provenance, CanonicalGlobalViewOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets view
      (lowerPlace owner (lowerEnv env.mod env.impl.vars returnTypes) initial).2 provenance) :
    CanonicalGlobalStatementOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets loop scope (.append owner view origin) initial upper := by
  intro occurrence cursor output start finish before after typed replay ceiling _sourceScopes _stack ready sites targets generated _loopTargets _loopReplay _counterTyped _included native metadata continuation
  obtain ⟨path, globalPath⟩ := occurrence
  obtain ⟨actualPath,located⟩ := cursor
  obtain ⟨info, element, writable, childStart, ownerTyped, _elementType, viewTyped, _writable, _⟩ := tyStmt_append_children typed
  obtain ⟨ownerRoots, ownerState, ownerReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  obtain ⟨viewRoots, viewState, viewReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp tail
  have sourceType := tyPlace_accessType tables.moduleEq.symm tables.variablesEq.symm ownerTyped
  obtain ⟨limited, limitedRun⟩ : ∃ limited, env.limitedOwner owner = .ok limited := by
    cases shape : info.ty <;> simp only [PEnv.limitedOwner, sourceType, shape] <;> first | exact ⟨false, rfl⟩ | exact ⟨true, rfl⟩
  have sourceEffect := rpStmt_append_effect ownerReplay viewReplay limitedRun replay
  have viewCeiling : EffectRefinement func viewState.eff target := by
    apply (growth_extension _ _ ownerRoots viewRoots env.mod.profile limited).trans
    simpa only [sourceEffect] using ceiling
  have ownerCeiling := effectRefinement_before_of_replay (rp_mono_all.2.1 env view)
    (rp_rebinds_mono_all.2.1 env view) (rp_flags_mono_all.2.1 env view) viewReplay viewCeiling
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let address := lowerPlace owner le initial
  let value := lowerView view le address.2
  have viewNative : NativeRows vt value.2 := native.of_prefix (types_emitEffect (.append address.1 value.1 (some origin)) le value.2 _ _ rfl)
  have viewMetadata := metadata.of_advance (advB_emitEffect (.append address.1 value.1 (some origin)) le value.2 _ _ rfl)
  have viewContinuation := continuation.of_advance (advB_emitEffect (.append address.1 value.1 (some origin)) le value.2 _ _ rfl)
  have ownerNative := viewNative.of_prefix (types_lowerView view le address.2 _ _ rfl)
  have ownerMetadata := viewMetadata.of_advance (advB_lowerView view le address.2 _ _ rfl)
  have ownerContinuation := viewContinuation.of_advance (advB_lowerView view le address.2 _ _ rfl)
  obtain ⟨middle, ownerReady, ownerValue, ownerPrefix, ownerLedger, ownerSites⟩ :=
    ownerChild ⟨path ++ [0], globalPath.snoc 0 rfl⟩ ⟨actualPath ++ [0],located.child rfl⟩ info start childStart before ownerState ownerRoots ownerTyped ownerReplay ownerCeiling ready sites targets generated ownerNative ownerMetadata ownerContinuation
  obtain ⟨next, viewReady, viewValue, viewPrefix, viewLedger, viewSites⟩ :=
    viewChild middle ⟨path ++ [1], globalPath.snoc 1 rfl⟩ ⟨actualPath ++ [1],located.child rfl⟩ (element, writable) childStart finish ownerState viewState viewRoots viewTyped viewReplay viewCeiling
      ownerReady ownerSites (targets.mono (advB_lowerPlace owner le initial _ _ rfl).ext) (generated.lowerPlace owner rfl) viewNative viewMetadata viewContinuation
  obtain ⟨mutability, actualType⟩ : ∃ mutability, value.2.cur.isSome = true →
      vt[address.1]? = some (some (.data (.ref mutability info.ty))) := by
    by_cases live : value.2.cur.isSome = true
    · obtain ⟨mutability, row⟩ := tables.occurrence_native_place_row ownerNative generated ownerTyped rfl
        ((dead_lowerView view).live_before rfl live)
      exact ⟨mutability, fun _ => row⟩
    · exact ⟨.readOnly, fun active => (live active).elim⟩
  have completed := viewReady.append loop ownerReplay viewReplay replay ceiling rfl rfl
    closed rfl
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
  have growth : middle.vals.size ≤ next.vals.size := by
    rw [ownerReady.roots.valueSize, viewReady.roots.valueSize]
    exact (advB_lowerView view le address.2 _ _ rfl).vals
  have placePath : DemandNodeAt (.statement (.append owner view origin)) [0] (.place owner) := .child rfl (.here _)
  have viewPath : DemandNodeAt (.statement (.append owner view origin)) [1] (.view view) := .child rfl (.here _)
  have step := occurrence_emitEffect_live (env := env) (root := .statement (.append owner view origin))
    (func := func) (types := vt) (upper := next)
    (rfl : emitEffect (.append address.1 value.1 (some origin)) le value.2 = _) (by
      intro live
      apply InstructionOccurrences.effect (ordinary := by intro address value origin same; cases same)
        (consumed := by
          intro operand member mutability payload reference
          have alternatives : operand = address.1 ∨ operand = value.1 := by
            simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Effect.uses] using member
          rcases alternatives with same | same
          · subst operand
            have ownerLive := (dead_lowerView view).live_before rfl live
            have oldBound : address.1 < middle.vals.size := ownerReady.roots.valueSize ▸ (ownerValue ownerLive).1
            refine .place address.1 env [0] owner before ownerRoots ownerState rfl placePath ownerReplay
              (Nat.lt_of_lt_of_le oldBound growth) ?_
            rw [viewPrefix address.1 oldBound]
            exact (ownerValue ownerLive).2
          · subst operand
            have viewRun : lowerView view (lowerEnv typingEnv.mod typingEnv.vars returnTypes) address.2 = value := by
              rw [← tables.moduleEq, ← tables.variablesEq]
            obtain ⟨viewMutability, row⟩ := viewNative.view (generated.lowerPlace owner (env := le) rfl)
              viewTyped viewRun live
            rw [row] at reference
            cases reference)
      intro operand member _
      have alternatives : operand = address.1 ∨ operand = value.1 := by
        simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Effect.uses] using member
      rcases alternatives with same | same
      · subst operand
        have ownerLive := (dead_lowerView view).live_before rfl live
        have oldBound : address.1 < middle.vals.size := ownerReady.roots.valueSize ▸ (ownerValue ownerLive).1
        apply OperandOccurrence.place placePath ownerReplay (Nat.lt_of_lt_of_le oldBound growth)
        rw [viewPrefix address.1 oldBound]
        exact (ownerValue ownerLive).2
      · subst operand
        exact OperandOccurrence.view viewPath viewReplay
          (viewReady.roots.valueSize ▸ (viewValue live).bound) (viewValue live).refined)
  have ledger := ((ownerLedger.retained growth viewPrefix).underRoot placePath).trans
    ((viewLedger.underRoot viewPath).trans step)
  have finalSites := viewSites.mutationEffect (effect := .append address.1 value.1 (some origin)) trivial (rfl : emitEffect (.append address.1 value.1 (some origin)) le value.2 = _)
    (Nat.le_refl _) (fun _ _ => rfl)
  exact ⟨next, completed, retained, fun expected => occurrence_mutation_transfer loop typed rfl ready retained, ledger, finalSites⟩

end Goose.Lower.Validation.SourceReplacementWriterLedger
