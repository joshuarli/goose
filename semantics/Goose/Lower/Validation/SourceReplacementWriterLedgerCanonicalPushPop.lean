import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceMutationsGrowth
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceMutationsOwners

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation ReplacementContentFlowSource

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}

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

theorem canonical_expressionOccurrence_push {owner : Place} {expression : Expr} (origin : Option OriginId)
    (tables : SourceRootTables typingEnv env) (readable : SourceReadableEnvironment typingEnv) (closed : ParameterRootsClosed func)
    (ownerChild : CanonicalGlobalPlaceOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets owner initial upper)
    (valueChild : ∀ provenance, CanonicalGlobalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets expression
      (lowerPlace owner (lowerEnv env.mod env.impl.vars returnTypes) initial).2 provenance) :
    CanonicalGlobalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets (.push owner expression origin) initial upper := by
  intro occurrence cursor type start finish before after roots typed replay ceiling ready sites targets generated native metadata continuation
  obtain ⟨path, globalPath⟩ := occurrence
  obtain ⟨actualPath,located⟩ := cursor
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
  have valueCeiling : EffectRefinement func valueState.eff target := by
    apply (growth_extension _ _ ownerRoots [] env.mod.profile limited).trans
    cases profile : env.mod.profile <;>
      simp [profile] at sourceEffect ⊢ <;> rw [sourceEffect] at ceiling <;>
      simpa [rootsTargets, addTargets] using ceiling
  have ownerCeiling := effectRefinement_before_expression valueReplay valueCeiling
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let address := lowerPlace owner le initial
  let value := lowerExpr expression le address.2
  have valueNative : NativeRows vt value.2 := native.of_prefix (types_emitDef (.push address.1 value.1 origin) le value.2 _ _ rfl)
  have valueMetadata := metadata.of_advance (advB_emitDef (.push address.1 value.1 origin) le value.2 _ _ rfl)
  have valueContinuation := continuation.of_advance (advB_emitDef (.push address.1 value.1 origin) le value.2 _ _ rfl)
  have ownerNative := valueNative.of_prefix (types_lowerExpr expression le address.2 _ _ rfl)
  have ownerMetadata := valueMetadata.of_advance (advB_lowerExpr expression le address.2 _ _ rfl)
  have ownerContinuation := valueContinuation.of_advance (advB_lowerExpr expression le address.2 _ _ rfl)
  obtain ⟨middle, ownerReady, ownerValue, ownerPrefix, ownerLedger, ownerSites⟩ :=
    ownerChild ⟨path ++ [0], globalPath.snoc 0 rfl⟩ ⟨actualPath ++ [0],located.child rfl⟩ info ownerStart ownerFinish before ownerState ownerRoots ownerTyped ownerReplay ownerCeiling ready sites targets generated ownerNative ownerMetadata ownerContinuation
  obtain ⟨valueUpper, valueReady, valueFacts, valuePrefix, valueLedger, valueSites⟩ :=
    valueChild middle ⟨path ++ [1], globalPath.snoc 1 rfl⟩ ⟨actualPath ++ [1],located.child rfl⟩ element childStart childFinish ownerState valueState valueRoots valueTyped valueReplay valueCeiling
      ownerReady ownerSites (targets.mono (advB_lowerPlace owner le initial _ _ rfl).ext) (generated.lowerPlace owner rfl) valueNative valueMetadata valueContinuation
  obtain ⟨mutability, actualType⟩ : ∃ mutability, value.2.cur.isSome = true →
      vt[address.1]? = some (some (.data (.ref mutability info.ty))) := by
    by_cases live : value.2.cur.isSome = true
    · obtain ⟨mutability, row⟩ := tables.occurrence_native_place_row ownerNative generated ownerTyped rfl
        ((dead_lowerExpr expression).live_before rfl live)
      exact ⟨mutability, fun _ => row⟩
    · exact ⟨.readOnly, fun active => (live active).elim⟩
  obtain ⟨next, completed, returned, retained⟩ := valueReady.push (element := element)
    ownerReplay valueReplay replay ceiling rfl rfl
    closed rfl
    (by intro candidate selected; subst origin; simpa only [le, lowerEnv, tables.moduleEq] using Core.tyExpr_push_success_origin_bound typed)
    sourceType actualType (by
      intro live
      have ownerLive := (dead_lowerExpr expression).live_before rfl live
      have oldBound := (ownerValue ownerLive).1
      refine ⟨Nat.lt_of_lt_of_le oldBound (advB_lowerExpr expression le address.2 _ _ rfl).vals,
        (valueFacts live).bound, ?_⟩
      rw [valuePrefix address.1 (by rw [ownerReady.roots.valueSize]; exact oldBound)]
      exact (ownerValue ownerLive).2)
  have initialPrefix : ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old := by
    intro old bound
    have ownerGrowth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, ownerReady.roots.valueSize]
      exact (advB_lowerPlace owner le initial _ _ rfl).vals
    have valueGrowth : middle.vals.size ≤ valueUpper.vals.size := by
      rw [ownerReady.roots.valueSize, valueReady.roots.valueSize]
      exact (advB_lowerExpr expression le address.2 _ _ rfl).vals
    exact (retained old (Nat.lt_of_lt_of_le bound (Nat.le_trans ownerGrowth valueGrowth))).trans
      ((valuePrefix old (Nat.lt_of_lt_of_le bound ownerGrowth)).trans (ownerPrefix old bound))
  have middleGrowth : middle.vals.size ≤ valueUpper.vals.size := by
    rw [ownerReady.roots.valueSize, valueReady.roots.valueSize]
    exact (advB_lowerExpr expression le address.2 _ _ rfl).vals
  have finalGrowth : valueUpper.vals.size ≤ next.vals.size := by
    rw [valueReady.roots.valueSize, completed.roots.valueSize]
    exact (advB_emitDef (.push address.1 value.1 origin) le value.2 _ _ rfl).vals
  have placePath : DemandNodeAt (.expression (.push owner expression origin)) [0] (.place owner) := .child rfl (.here _)
  have valuePath : DemandNodeAt (.expression (.push owner expression origin)) [1] (.expression expression) := .child rfl (.here _)
  have operands (live : value.2.cur.isSome = true) :
      OperandOccurrence env (.expression (.push owner expression origin)) func next address.1 ∧
      OperandOccurrence env (.expression (.push owner expression origin)) func next value.1 := by
    have ownerLive := (dead_lowerExpr expression).live_before rfl live
    have oldBound : address.1 < middle.vals.size := ownerReady.roots.valueSize ▸ (ownerValue ownerLive).1
    have middleBound := Nat.lt_of_lt_of_le oldBound middleGrowth
    refine ⟨OperandOccurrence.place placePath ownerReplay (Nat.lt_of_lt_of_le middleBound finalGrowth) ?_,
      OperandOccurrence.expression valuePath valueReplay ?_ ?_⟩
    · rw [retained address.1 middleBound, valuePrefix address.1 oldBound]
      exact (ownerValue ownerLive).2
    · exact Nat.lt_of_lt_of_le (valueReady.roots.valueSize ▸ (valueFacts live).bound) finalGrowth
    · rw [retained value.1 (valueReady.roots.valueSize ▸ (valueFacts live).bound)]
      exact (valueFacts live).refined
  have step := occurrence_emitDef_live (env := env) (root := .expression (.push owner expression origin))
    (func := func) (types := vt) (upper := next)
    (rfl : emitDef (.push address.1 value.1 origin) le value.2 = _) (by
      intro live
      apply InstructionOccurrences.definition
      · intro operand member _
        have alternatives : operand = address.1 ∨ operand = value.1 := by
          simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] using member
        rcases alternatives with same | same
        · subst operand; exact (operands live).1
        · subst operand; exact (operands live).2
      · intro address same; cases same
      · intro fn args origin same; cases same
      · intro operand member mutability payload reference
        have alternatives : operand = address.1 ∨ operand = value.1 := by
          simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] using member
        rcases alternatives with same | same
        · subst operand
          have ownerLive := (dead_lowerExpr expression).live_before rfl live
          have oldBound : address.1 < middle.vals.size := ownerReady.roots.valueSize ▸ (ownerValue ownerLive).1
          have middleBound := Nat.lt_of_lt_of_le oldBound middleGrowth
          refine .place address.1 env [0] owner before ownerRoots ownerState rfl placePath ownerReplay
            (Nat.lt_of_lt_of_le middleBound finalGrowth) ?_
          rw [retained address.1 middleBound, valuePrefix address.1 oldBound]
          exact (ownerValue ownerLive).2
        · subst operand
          have row := tables.occurrence_native_expression_row valueNative
            (generated.lowerPlace owner (env := le) rfl) valueTyped (rfl : lowerExpr expression le address.2 = value) live
          have allowed := source_place_paramOk owner readable ownerTyped
          have flat : element.flat = true := occurrence_owner_element_flat allowed _elementType
          rw [row] at reference
          have shape : element = .ref mutability payload := VTy.data.inj (Option.some.inj (Option.some.inj reference))
          simp [shape, Ty.flat] at flat)
  have ledger := (((ownerLedger.retained middleGrowth valuePrefix).retained finalGrowth retained).underRoot placePath).trans
    (((valueLedger.retained finalGrowth retained).underRoot valuePath).trans step)
  have finalSites := valueSites.emitDef (rfl : emitDef (.push address.1 value.1 origin) le value.2 = _) finalGrowth retained
  exact ⟨next, completed, returned, initialPrefix, ledger, finalSites⟩

theorem canonical_expressionOccurrence_pop {owner : Place} (origin : OriginId)
    (tables : SourceRootTables typingEnv env) (closed : ParameterRootsClosed func)
    (child : CanonicalGlobalPlaceOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets owner initial upper) :
    CanonicalGlobalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets (.pop owner origin) initial upper := by
  intro occurrence cursor type start finish before after roots typed replay ceiling ready sites targets generated native metadata continuation
  obtain ⟨path, globalPath⟩ := occurrence
  obtain ⟨actualPath,located⟩ := cursor
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
    child ⟨path ++ [0], globalPath.snoc 0 rfl⟩ ⟨actualPath ++ [0],located.child rfl⟩ info ownerStart ownerFinish before ownerState ownerRoots ownerTyped ownerReplay ownerCeiling ready sites targets generated ownerNative ownerMetadata ownerContinuation
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

#print axioms canonical_expressionOccurrence_push
#print axioms canonical_expressionOccurrence_pop

end Goose.Lower.Validation.SourceReplacementWriterLedger
