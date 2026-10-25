import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceMutationsCommon
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceSitePublish

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem statementOccurrence_assignWhole {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)}
    {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId}
    {initial : LS} {upper : Prov} {owner : Place} {expression : Expr}
    (origin : OriginId) (loop : Option LoopCtx) (scope : ScopeId)
    (tables : SourceRootTables typingEnv env) (closed : ParameterRootsClosed func)
    (ownerChild : GlobalPlaceOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount
      siteRoot siteTargets owner initial upper)
    (valueChild : ∀ provenance, GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount
      siteRoot siteTargets expression
      (emitEffect (.clear (lowerPlace owner (lowerEnv env.mod env.impl.vars returnTypes) initial).1 (some origin))
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerPlace owner (lowerEnv env.mod env.impl.vars returnTypes) initial).2).2 provenance) :
    GlobalStatementOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
      loop scope (.assignWhole owner expression origin) initial upper := by
  intro occurrence output start finish before after typed replay ceiling _scopes _stack ready sites targets generated _loop _bounds _counter _included native metadata continuation
  obtain ⟨path, globalPath⟩ := occurrence
  obtain ⟨info, element, childStart, ownerTyped, _shape, valueTyped, _binding, _contents, _⟩ := tyStmt_assignWhole_children typed
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
  let cleared := emitEffect (.clear address.1 (some origin)) le address.2
  let value := lowerExpr expression le cleared.2
  let published := emitEffect (.replace address.1 value.1 (some origin)) le value.2
  have whole : lowerStmt loop (.assignWhole owner expression origin) le initial = published := rfl
  have valueNative : NativeRows vt value.2 := native.of_prefix
    (types_emitEffect (.replace address.1 value.1 (some origin)) le value.2 _ _ rfl)
  have valueMetadata := metadata.of_advance
    (advB_emitEffect (.replace address.1 value.1 (some origin)) le value.2 _ _ rfl)
  have valueContinuation := continuation.of_advance
    (advB_emitEffect (.replace address.1 value.1 (some origin)) le value.2 _ _ rfl)
  have clearNative := valueNative.of_prefix (types_lowerExpr expression le cleared.2 _ _ rfl)
  have clearMetadata := valueMetadata.of_advance (advB_lowerExpr expression le cleared.2 _ _ rfl)
  have clearContinuation := valueContinuation.of_advance (advB_lowerExpr expression le cleared.2 _ _ rfl)
  have ownerNative := clearNative.of_prefix (types_emitEffect (.clear address.1 (some origin)) le address.2 _ _ rfl)
  have ownerMetadata := clearMetadata.of_advance (advB_emitEffect (.clear address.1 (some origin)) le address.2 _ _ rfl)
  have ownerContinuation := clearContinuation.of_advance (advB_emitEffect (.clear address.1 (some origin)) le address.2 _ _ rfl)
  obtain ⟨middle, ownerReady, ownerValue, ownerPrefix, ownerLedger, ownerSites⟩ := ownerChild
    ⟨path ++ [0], globalPath.snoc 0 rfl⟩ info start childStart before ownerState ownerRoots
    ownerTyped ownerReplay ownerCeiling ready sites targets generated ownerNative ownerMetadata ownerContinuation
  have originBound : origin < le.mod.origins.size := tables.mutation_origin_bound typed
  have clearedReady : ReplayBuilder (lower env.mod) results vt func target le scopeCount slots cleared.2 middle := by
    apply ownerReady.emitEffect_live (.clear address.1 (some origin))
    · intro live
      apply Inst.SymbolsWithin.eff
      · simpa [Effect.uses] using (ownerValue live).1
      · simpa [Effect.origin] using originBound
      · trivial
    · intros; trivial
    · intro live
      exact (effectStep_clear_refines closed (effectRefinement_empty func ownerState.eff) (ownerValue live).2).trans clearCeiling
  have placePath : DemandNodeAt (.statement (.assignWhole owner expression origin)) [0] (.place owner) := .child rfl (.here _)
  have valuePath : DemandNodeAt (.statement (.assignWhole owner expression origin)) [1] (.expression expression) := .child rfl (.here _)
  have clearLedger := occurrence_emitEffect_live (env := env) (root := .statement (.assignWhole owner expression origin))
    (func := func) (types := vt) (upper := middle) (rfl : emitEffect (.clear address.1 (some origin)) le address.2 = cleared)
    (by
      intro live
      apply InstructionOccurrences.effect (ordinary := by intro address value origin same; cases same)
        (consumed := by
          intro operand member _ _ _
          have same : operand = address.1 := by simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Effect.uses] using member
          subst operand
          exact .place address.1 env [0] owner before ownerRoots ownerState rfl placePath ownerReplay
            (ownerReady.roots.valueSize ▸ (ownerValue live).1) (ownerValue live).2)
      intro operand member _
      have same : operand = address.1 := by simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Effect.uses] using member
      subst operand
      exact OperandOccurrence.place placePath ownerReplay
        (ownerReady.roots.valueSize ▸ (ownerValue live).1) (ownerValue live).2)
  have clearSites := ownerSites.mutationEffect (effect := .clear address.1 (some origin)) trivial rfl
    (Nat.le_refl _) (fun _ _ => rfl)
  have ownerGenerated := generated.lowerPlace owner (env := le) rfl
  have clearGenerated := ownerGenerated.emitEffect (.clear address.1 (some origin))
    (rfl : emitEffect (.clear address.1 (some origin)) le address.2 = cleared)
  have ownerAdvance := advB_lowerPlace owner le initial _ _ rfl
  have clearAdvance := advB_emitEffect (.clear address.1 (some origin)) le address.2 _ _ rfl
  have valueAdvance := advB_lowerExpr expression le cleared.2 _ _ rfl
  have publishAdvance := advB_emitEffect (.replace address.1 value.1 (some origin)) le value.2 _ _ rfl
  obtain ⟨next, valueReady, valueFacts, valuePrefix, valueLedger, valueSites⟩ := valueChild middle
    ⟨path ++ [1], globalPath.snoc 1 rfl⟩ info.ty childStart finish _ valueState valueRoots valueTyped valueReplay
    valueCeiling clearedReady clearSites ((targets.mono ownerAdvance.ext).mono clearAdvance.ext) clearGenerated valueNative valueMetadata valueContinuation
  have liveInfo (live : value.2.cur.isSome = true) : address.2.cur.isSome = true ∧ address.1 < value.2.vals.size := by
    have clearLive := (dead_lowerExpr expression).live_before rfl live
    have ownerLive := (dead_emitEffect (.clear address.1 (some origin))).live_before rfl clearLive
    exact ⟨ownerLive, Nat.lt_of_lt_of_le (ownerValue ownerLive).1 (Nat.le_trans clearAdvance.vals valueAdvance.vals)⟩
  have growth : middle.vals.size ≤ next.vals.size := by
    rw [clearedReady.roots.valueSize, valueReady.roots.valueSize]
    exact valueAdvance.vals
  have ownerOccurrence (live : value.2.cur.isSome = true) :
      OperandOccurrence env (.statement (.assignWhole owner expression origin)) func next address.1 := by
    have bound : address.1 < middle.vals.size := ownerReady.roots.valueSize ▸ (ownerValue (liveInfo live).1).1
    apply OperandOccurrence.place placePath ownerReplay (Nat.lt_of_lt_of_le bound growth)
    rw [valuePrefix address.1 bound]
    exact (ownerValue (liveInfo live).1).2
  have completed : ReplayBuilder (lower env.mod) results vt func target le scopeCount slots published.2 next := by
    apply valueReady.emitEffect_live (.replace address.1 value.1 (some origin))
    · intro live
      apply Inst.SymbolsWithin.eff
      · simpa [Effect.uses] using And.intro (liveInfo live).2 (valueFacts live).bound
      · simpa [Effect.origin] using originBound
      · trivial
    · intros; trivial
    · intro live
      have roots : GIR.RootsRefine func (rootsAt next.vals address.1) ownerRoots := by
        rw [valuePrefix address.1 (ownerReady.roots.valueSize ▸ (ownerValue (liveInfo live).1).1)]
        exact (ownerValue (liveInfo live).1).2
      have delta := effectStep_replace_refines (module := lower env.mod) (vt := vt) (value := value.1)
        (origin := some origin) closed (effectRefinement_empty func valueState.eff) roots
      have cleanup : EffectRefinement func
          { valueState.eff with
            reads := addTargets valueState.eff.reads (rootsTargets ownerRoots)
            writes := addTargets valueState.eff.writes (rootsTargets ownerRoots)
            grows := addTargets valueState.eff.grows (rootsTargets ownerRoots)
            shrinks := addTargets valueState.eff.shrinks (rootsTargets ownerRoots) } after.eff := by
        rw [sourceEffect]
        refine ⟨?_, fun _ h => h, fun _ h => h, ?_, fun _ h => h, fun h => h, fun h => h, fun h => h⟩
        · apply storageTargets_mono
          intro t member
          rcases mem_addTargets_iff.mp member with old | added
          · exact old
          · exact (rpExpr_mono valueReplay).2.1 t (addTargets_right _ _ t added)
        · apply storageTargets_mono
          intro t member
          rcases mem_addTargets_iff.mp member with old | added
          · exact old
          · exact (rpExpr_mono valueReplay).2.2.2.2.1 t (addTargets_right _ _ t added)
      exact delta.trans (cleanup.trans ceiling)
  have replaceLedger := occurrence_emitEffect_live (env := env) (root := .statement (.assignWhole owner expression origin))
    (func := func) (types := vt) (upper := next) (rfl : emitEffect (.replace address.1 value.1 (some origin)) le value.2 = published)
    (by
      intro live
      apply InstructionOccurrences.effect (ordinary := by intro address value origin same; cases same)
        (consumed := by
          intro operand member mutability payload reference
          have alternatives : operand = address.1 ∨ operand = value.1 := by
            simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Effect.uses] using member
          rcases alternatives with same | same
          · subst operand
            have bound : address.1 < middle.vals.size := ownerReady.roots.valueSize ▸ (ownerValue (liveInfo live).1).1
            refine .place address.1 env [0] owner before ownerRoots ownerState rfl placePath ownerReplay
              (Nat.lt_of_lt_of_le bound growth) ?_
            rw [valuePrefix address.1 bound]
            exact (ownerValue (liveInfo live).1).2
          · subst operand
            have row := tables.occurrence_native_expression_row valueNative clearGenerated valueTyped
              (rfl : lowerExpr expression le cleared.2 = value) live
            rw [row] at reference
            rcases _shape with shape | shape <;> simp [shape] at reference)
      intro operand member _
      have alternatives : operand = address.1 ∨ operand = value.1 := by
        simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Effect.uses] using member
      rcases alternatives with same | same
      · subst operand; exact ownerOccurrence live
      · subst operand
        exact OperandOccurrence.expression valuePath valueReplay
          (valueReady.roots.valueSize ▸ (valueFacts live).bound) (valueFacts live).refined)
  have avoids : IntervalTargetsAvoid cleared.2 value.2 siteTargets := by
    intro t member
    exact Or.inl (Nat.lt_of_lt_of_le (targets t member) (ownerAdvance.ext.trans clearAdvance.ext).1)
  have framed : IntervalEdgesFramed cleared.2 value.2 published.2 :=
    ReplacementIntervalsPreserved.of_run (targets := siteTargets) (generatedTargetFrame_emitEffect none _)
      (rfl : emitEffect (.replace address.1 value.1 (some origin)) le value.2 = published)
      cleared.2 value.2 (.refl _) avoids (.refl _ _)
  have siteTypes := (types_emitEffect (.clear address.1 (some origin)) le address.2 _ _ rfl).trans
    ((types_lowerExpr expression le cleared.2 _ _ rfl).trans (types_emitEffect (.replace address.1 value.1 (some origin)) le value.2 _ _ rfl))
  have finalSites := valueSites.emitReplacement (rfl : emitEffect (.replace address.1 value.1 (some origin)) le value.2 = published)
    (Nat.le_refl _) (fun _ _ => rfl) (by
      intro block body current row
      have live : value.2.cur.isSome = true := by rw [current]; rfl
      refine ⟨{
        source := {
          site := {
            source := {
              sourceEnv := typingEnv
              results := returnTypes
              environment := by rw [← tables.moduleEq, ← tables.variablesEq]
              place := owner
              rhs := expression
              scope := scope
              start := start
              finish := finish
              output := output
              accepted := typed
              sourceRoot := siteRoot
              sourcePath := path
              structuralSource := globalPath
              initial := initial
              finished := published.2
              site := {
                owner := address.1
                value := value.1
                addressed := address.2
                cleared := cleared.2
                captured := value.2
                addressRun := rfl
                clearRun := rfl
                rhsRun := rfl
                publishRun := rfl }
              owner_eq := rfl
              value_eq := rfl
              generated := generated
              live := live
              extension := .refl _
              types := siteTypes
              framed := framed }
            capturedBody := body
            current := current
            row := row
            position_eq := rfl }
          avoids := avoids
          root_eq := rfl }
        localEnv := env
        access := rfl
        before := before
        ownerRoots := ownerRoots
        addressed := ownerState
        ownerReplay := ownerReplay
        ownerBound := valueReady.roots.valueSize ▸ (liveInfo live).2
        ownerRefined := by
          rw [valuePrefix address.1 (ownerReady.roots.valueSize ▸ (ownerValue (liveInfo live).1).1)]
          exact (ownerValue (liveInfo live).1).2
        rhs := valueLedger
        clearedOperandUses := fun inst member input used =>
          (clearedReady.symbols.instructions inst member).uses input used }⟩)
  have retained (old : Nat) (bound : old < upper.vals.size) : rootsAt next.vals old = rootsAt upper.vals old := by
    have ownerGrowth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, ownerReady.roots.valueSize]
      exact ownerAdvance.vals
    exact (valuePrefix old (Nat.lt_of_lt_of_le bound ownerGrowth)).trans (ownerPrefix old bound)
  have ledger := ((ownerLedger.retained growth valuePrefix).underRoot placePath).trans
    ((clearLedger.retained growth valuePrefix).trans ((valueLedger.underRoot valuePath).trans replaceLedger))
  exact ⟨next, completed, retained, (fun expected => occurrence_mutation_transfer loop typed rfl ready retained), ledger, finalSites⟩

end Goose.Lower.Validation.ReplacementContentFlowSource
