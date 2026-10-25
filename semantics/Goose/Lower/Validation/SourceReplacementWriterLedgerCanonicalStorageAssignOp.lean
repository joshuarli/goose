import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceStorageAssignOpActions

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation ReplacementContentFlowSource

private theorem integerType_preserves (value : ValueId) (le : LEnv) (state : LS) :
    ∃ ty, intTyOf value le state = (ty, state) := by
  simp only [intTyOf, bind_run]
  generalize row : valTy value le state = pair
  have same : pair.2 = state := row ▸ valTy_run value le state
  obtain ⟨type, next⟩ := pair
  cases type <;> simp_all [pure_run]
  case data type => cases type <;> simp_all [pure_run]

theorem canonical_statementOccurrence_assignOp {ownerRoot : Fragment} {ownerInitial baseline : LS} {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
    {siteRoot : DemandNode} {siteTargets : List BlockId}
    {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}
    {place : Place} {expression : Expr} (operation : BinOp) (origin : OriginId) (loop : Option LoopCtx) (scope : ScopeId)
    (tables : SourceRootTables typingEnv env)
    (closed : ParameterRootsClosed func)
    (placeChild : CanonicalGlobalPlaceOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets place initial upper)
    (valueChild : ∀ provenance, CanonicalGlobalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets expression
      (Goose.Lower.emitDef (.load (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).1)
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).2).2 provenance) :
    CanonicalGlobalStatementOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets loop scope (.assignOp operation place expression origin) initial upper := by
  intro occurrence cursor output start finish before after typed replay ceiling _sourceScopes _stack ready sites targets generated _loopTargets _loopReplay _counter _included native metadata continuation
  obtain ⟨path, globalPath⟩ := occurrence
  obtain ⟨actualPath,located⟩ := cursor
  obtain ⟨info, integer, childStart, placeTyped, infoType, valueTyped, _binding, _⟩ := tyStmt_assignOp_children typed
  obtain ⟨placeRoots, placeState, placeReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  obtain ⟨valueRoots, valueState, valueReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp tail
  have sourceReplay := replay
  rw [rpStmt_assignOp_after_operands placeReplay valueReplay] at sourceReplay
  have sourceEffect := congrArg (fun pair => pair.2.eff) (Except.ok.inj sourceReplay).symm
  have valueCeiling : EffectRefinement (func) valueState.eff target := by
    apply EffectRefinement.trans (middle := after.eff) ?_ ceiling
    rw [sourceEffect]
    refine ⟨?_, ?_, fun _ h => h, fun _ h => h, fun _ h => h, ?_, fun h => h, fun h => h⟩
    · exact storageTargets_mono (fun t h => addTargets_left _ _ t h)
    · exact storageTargets_mono (fun t h => addTargets_left _ _ t h)
    · intro h
      cases aborts : operation.mayAbort <;> simp [h]
  have placeCeiling := effectRefinement_before_expression valueReplay valueCeiling
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let address := lowerPlace place le initial
  let loaded := Goose.Lower.emitDef (.load address.1) le address.2
  let value := lowerExpr expression le loaded.2
  have actualType := integerType_preserves loaded.1 le value.2
  obtain ⟨runtimeType, typeRun⟩ := actualType
  have whole := lowerStmt_assignOp_after_rhs (op := operation) (org := origin) loop
    (rfl : lowerPlace place le initial = address) (rfl : Goose.Lower.emitDef (.load address.1) le address.2 = loaded)
    (rfl : lowerExpr expression le loaded.2 = value) typeRun
  have valueNative : NativeRows vt value.2 := by
    rw [whole] at native
    exact (native.of_prefix (types_emitEffect (.store address.1
      (Goose.Lower.emitDef (.bin operation runtimeType loaded.1 value.1 (some origin)) le value.2).1 (some origin)) le _ _ _ rfl)).of_prefix
      (types_emitDef (.bin operation runtimeType loaded.1 value.1 (some origin)) le value.2 _ _ rfl)
  have valueMetadata : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func value.2 := by
    rw [whole] at metadata
    exact (metadata.of_advance (advB_emitEffect (.store address.1
      (Goose.Lower.emitDef (.bin operation runtimeType loaded.1 value.1 (some origin)) le value.2).1 (some origin)) le _ _ _ rfl)).of_advance
      (advB_emitDef (.bin operation runtimeType loaded.1 value.1 (some origin)) le value.2 _ _ rfl)
  have valueContinuation : NativeBuilderContinuation func value.2 := by
    rw [whole] at continuation
    exact (continuation.of_advance (advB_emitEffect (.store address.1
      (Goose.Lower.emitDef (.bin operation runtimeType loaded.1 value.1 (some origin)) le value.2).1 (some origin)) le _ _ _ rfl)).of_advance
      (advB_emitDef (.bin operation runtimeType loaded.1 value.1 (some origin)) le value.2 _ _ rfl)
  have loadNative := valueNative.of_prefix (types_lowerExpr expression le loaded.2 _ _ rfl)
  have loadMetadata := valueMetadata.of_advance (advB_lowerExpr expression le loaded.2 _ _ rfl)
  have loadContinuation := valueContinuation.of_advance (advB_lowerExpr expression le loaded.2 _ _ rfl)
  have placeNative := loadNative.of_prefix (types_emitDef (.load address.1) le address.2 _ _ rfl)
  have placeMetadata := loadMetadata.of_advance (advB_emitDef (.load address.1) le address.2 _ _ rfl)
  have placeContinuation := loadContinuation.of_advance (advB_emitDef (.load address.1) le address.2 _ _ rfl)
  obtain ⟨middle, placeReady, placeValue, placePrefix, placeLedger, placeSites⟩ := placeChild ⟨path ++ [0], globalPath.snoc 0 rfl⟩ ⟨actualPath ++ [0],located.child rfl⟩ info start childStart before placeState placeRoots
    placeTyped placeReplay placeCeiling ready sites targets generated placeNative placeMetadata placeContinuation
  have originBound : origin < le.mod.origins.size := tables.mutation_origin_bound typed
  have ownerNonref (live : address.2.cur.isSome = true) : (ownerTy vt address.1).any Ty.isRefLike = false := by
    obtain ⟨mu, row⟩ := tables.occurrence_native_place_row placeNative generated placeTyped rfl live
    change (ownerTy vt (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).1).any Ty.isRefLike = false
    simp [ownerTy, row, infoType, Ty.isRefLike]
  have scalarLoad (live : address.2.cur.isSome = true) : valRefLike vt loaded.1 = false := by
    have sourceRun : lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars returnTypes) initial = address := by
      rw [← tables.moduleEq, ← tables.variablesEq]
    obtain ⟨mu, row⟩ := lowerPlace_generated_typed place placeTyped sourceRun live generated
    have row' : address.2.vals[address.1]? = some (some (.data (.ref mu (.int integer)))) := by simpa only [infoType] using row
    cases current : address.2.cur with
    | none => simp [current] at live
    | some block =>
      have resultType : (Op.load address.1).resultTy (tyEnv le address.2) = .ok (.data (.int integer)) := by
        simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, row', pure, Except.pure, bind, Except.bind]
      have recorded : loaded.1 = address.2.vals.size ∧ loaded.2.cur = address.2.cur ∧
          loaded.2.vals[loaded.1]? = some (some (.data (.int integer))) ∧
          (∀ old, old < address.2.vals.size → loaded.2.vals[old]? = address.2.vals[old]?) :=
        emitDef_recorded (le := le) current resultType
      have nativeRow := loadNative _ _ recorded.2.2.1
      simp only [valRefLike, nativeRow, VTy.refLike, Ty.isRefLike]
  obtain ⟨loadedUpper, loadedReady, oldValue, loadPrefix⟩ := placeReady.emitTypedDef_live (.load address.1) [] (.data (.int .i64))
    (by intro live; simpa [Op.uses] using (placeValue live).1)
    (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
    (by
      intro live
      exact (occurrenceAssignOp_instruction_effects (func := func) (vt := vt) (loadRoots := middle) (storeRoots := middle)
        (old := address.2.vals.size) (rhs := value.1) (result := address.2.vals.size) (ty := .i64)
        closed placeReplay valueReplay replay (placeValue live).2 (placeValue live).2 (ownerNonref live) ceiling).1)
    (by
      intro live
      obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
      have identifier : loaded.1 = address.2.vals.size := by
        change (emitDef (.load address.1) le address.2).1 = address.2.vals.size
        rw [emitDef_run _ _ current]
      have scalar := scalarLoad live
      rw [identifier] at scalar
      change GIR.RootsRefine func (rootsOfDef results vt func middle address.2.vals.size (.load address.1)) []
      unfold rootsOfDef
      rw [scalar]
      exact GIR.RootsRefine.refl _ _)
    (by
      intro live _
      obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
      have identifier : loaded.1 = address.2.vals.size := by
        change (emitDef (.load address.1) le address.2).1 = address.2.vals.size
        rw [emitDef_run _ _ current]
      have scalar := scalarLoad live
      rw [identifier] at scalar
      change rootsOfDef results vt func middle address.2.vals.size (.load address.1) = []
      unfold rootsOfDef
      rw [scalar]
      rfl)
  have loadGrowth : middle.vals.size ≤ loadedUpper.vals.size := by
    rw [placeReady.roots.valueSize, loadedReady.roots.valueSize]
    exact (advB_emitDef (.load address.1) le address.2 _ _ rfl).vals
  have placePath : DemandNodeAt (.statement (.assignOp operation place expression origin)) [0] (.place place) := .child rfl (.here _)
  have valuePath : DemandNodeAt (.statement (.assignOp operation place expression origin)) [1] (.expression expression) := .child rfl (.here _)
  have loadLedger := occurrence_emitDef_live (env := env) (root := .statement (.assignOp operation place expression origin))
    (func := func) (types := vt) (upper := loadedUpper) (rfl : emitDef (.load address.1) le address.2 = loaded) (by
      intro live
      refine ⟨?_, ?_, ?_, InstructionOccurrences.no_store (by intro a v o same; cases same), ?_⟩
      · intro operand member _
        have same : operand = address.1 := by simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] using member
        subst operand
        have bounded : address.1 < middle.vals.size := placeReady.roots.valueSize ▸ (placeValue live).1
        apply OperandOccurrence.place placePath placeReplay (Nat.lt_of_lt_of_le bounded loadGrowth)
        rw [loadPrefix address.1 bounded]
        exact (placeValue live).2
      · intro result address' same reference
        have identifier : loaded.1 = address.2.vals.size := by
          cases current : address.2.cur with
          | none => simp [current] at live
          | some block =>
            change (emitDef (.load address.1) le address.2).1 = address.2.vals.size
            rw [emitDef_run _ _ current]
        have scalar := scalarLoad live
        rw [identifier] at scalar
        cases same
        rw [scalar] at reference
        cases reference
      · intro result fn args origin same
        cases same
      · intro operand member _ _ _
        have same : operand = address.1 := by simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] using member
        subst operand
        have bounded : address.1 < middle.vals.size := placeReady.roots.valueSize ▸ (placeValue live).1
        refine .place address.1 env [0] place before placeRoots placeState rfl placePath placeReplay
          (Nat.lt_of_lt_of_le bounded loadGrowth) ?_
        rw [loadPrefix address.1 bounded]
        exact (placeValue live).2)
  have loadedSites := placeSites.emitDef (rfl : emitDef (.load address.1) le address.2 = loaded) loadGrowth loadPrefix
  have placeAdvance := advB_lowerPlace place le initial _ _ rfl
  have loadAdvance := advB_emitDef (.load address.1) le address.2 _ _ rfl
  have rhsAdvance := advB_lowerExpr expression le loaded.2 _ _ rfl
  obtain ⟨rhsUpper, rhsReady, rhsValue, rhsPrefix, rhsLedger, rhsSites⟩ := valueChild loadedUpper
    ⟨path ++ [1], globalPath.snoc 1 rfl⟩ ⟨actualPath ++ [1],located.child rfl⟩ (.int integer) childStart finish placeState valueState valueRoots valueTyped valueReplay valueCeiling
    loadedReady loadedSites ((targets.mono placeAdvance.ext).mono loadAdvance.ext)
    ((generated.lowerPlace place (env := le) rfl).emitDef (.load address.1) (rfl : emitDef _ le address.2 = loaded)) valueNative valueMetadata valueContinuation
  have rhsGrowth : loadedUpper.vals.size ≤ rhsUpper.vals.size := by
    rw [loadedReady.roots.valueSize, rhsReady.roots.valueSize]
    exact rhsAdvance.vals
  have initialLive (live : value.2.cur.isSome = true) : address.2.cur.isSome = true :=
    (dead_emitDef (.load address.1)).live_before rfl ((dead_lowerExpr expression).live_before rfl live)
  have ownerBound (live : value.2.cur.isSome = true) : address.1 < value.2.vals.size :=
    Nat.lt_of_lt_of_le (placeValue (initialLive live)).1 (Nat.le_trans loadAdvance.vals rhsAdvance.vals)
  have oldBound (live : value.2.cur.isSome = true) : loaded.1 < value.2.vals.size :=
    Nat.lt_of_lt_of_le (oldValue ((dead_lowerExpr expression).live_before rfl live)).bound rhsAdvance.vals
  have rhsOwner (live : value.2.cur.isSome = true) : GIR.RootsRefine func (rootsAt rhsUpper.vals address.1) placeRoots := by
    have beforeBound : address.1 < middle.vals.size := placeReady.roots.valueSize ▸ (placeValue (initialLive live)).1
    rw [rhsPrefix address.1 (Nat.lt_of_lt_of_le beforeBound loadGrowth), loadPrefix address.1 beforeBound]
    exact (placeValue (initialLive live)).2
  obtain ⟨next, completed, finalPrefix⟩ := ReplayBuilder.occurrenceAssignOpAfterRhs loop closed rhsReady placeReplay valueReplay replay ceiling
    rfl rfl rfl typeRun originBound (by intro live; exact ⟨ownerBound live, oldBound live, (rhsValue live).bound, rhsOwner live, ownerNonref (initialLive live)⟩)
  let operationRun := emitDef (.bin operation runtimeType loaded.1 value.1 (some origin)) le value.2
  have finalNative : NativeRows vt operationRun.2 := by
    rw [whole] at native
    exact native.of_prefix (types_emitEffect (.store address.1 operationRun.1 (some origin)) le operationRun.2 _ _ rfl)
  have operationGrowth := advB_emitDef (.bin operation runtimeType loaded.1 value.1 (some origin)) le value.2 _ _ rfl
  have finalGrowth : rhsUpper.vals.size ≤ next.vals.size := by
    rw [rhsReady.roots.valueSize, completed.roots.valueSize, whole]
    exact (operationGrowth.trans (advB_emitEffect (.store address.1 operationRun.1 (some origin)) le operationRun.2 _ _ rfl)).vals
  have ownerOccurrence (live : value.2.cur.isSome = true) :
      OperandOccurrence env (.statement (.assignOp operation place expression origin)) func next address.1 := by
    have bounded : address.1 < rhsUpper.vals.size := rhsReady.roots.valueSize ▸ ownerBound live
    apply OperandOccurrence.place placePath placeReplay (Nat.lt_of_lt_of_le bounded finalGrowth)
    rw [finalPrefix address.1 bounded]
    exact rhsOwner live
  have binLedger := occurrence_emitDef_live (env := env) (root := .statement (.assignOp operation place expression origin))
    (func := func) (types := vt) (upper := next) (rfl : emitDef (.bin operation runtimeType loaded.1 value.1 (some origin)) le value.2 = operationRun) (by
      intro live
      apply InstructionOccurrences.definition
      · intro operand member reference
        have alternatives : operand = loaded.1 ∨ operand = value.1 := by simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] using member
        rcases alternatives with same | same
        · subst operand
          rw [scalarLoad (initialLive live)] at reference
          cases reference
        · subst operand
          have bounded : value.1 < rhsUpper.vals.size := rhsReady.roots.valueSize ▸ (rhsValue live).bound
          apply OperandOccurrence.expression valuePath valueReplay (Nat.lt_of_lt_of_le bounded finalGrowth)
          rw [finalPrefix value.1 bounded]
          exact (rhsValue live).refined
      · intro address same; cases same
      · intro fn args origin same; cases same
      · intro operand member mutability payload reference
        have alternatives : operand = loaded.1 ∨ operand = value.1 := by
          simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] using member
        rcases alternatives with same | same
        · subst operand
          have scalar := scalarLoad (initialLive live)
          simp [valRefLike, reference, VTy.refLike, Ty.isRefLike] at scalar
        · subst operand
          have row := tables.occurrence_native_expression_row valueNative
            ((generated.lowerPlace place (env := le) rfl).emitDef (.load address.1) (rfl : emitDef _ le address.2 = loaded))
            valueTyped (rfl : lowerExpr expression le loaded.2 = value) live
          rw [row] at reference
          cases reference)
  have storeLedger := occurrence_emitEffect_live (env := env) (root := .statement (.assignOp operation place expression origin))
    (func := func) (types := vt) (upper := next) (rfl : emitEffect (.store address.1 operationRun.1 (some origin)) le operationRun.2 = _) (by
      intro live
      have rhsLive := (dead_emitDef (.bin operation runtimeType loaded.1 value.1 (some origin))).live_before rfl live
      refine InstructionOccurrences.store ?_ ?_ ?_
      · intro operand member _
        have same : operand = address.1 := by simpa [GIR.ReplacementContentFlow.Model.accessOperands] using member
        subst operand
        exact ownerOccurrence rhsLive
      · intro reference
        have scalar : valRefLike vt operationRun.1 = false := ReplayBuilder.native_bin_nonref finalNative (rfl : emitDef _ le value.2 = operationRun) rhsLive
        exact Bool.noConfusion (scalar.symm.trans reference)
      · intro operand member _ _ _
        have same : operand = address.1 := by simpa [GIR.ReplacementContentFlow.Model.accessOperands] using member
        subst operand
        have bounded : address.1 < rhsUpper.vals.size := rhsReady.roots.valueSize ▸ ownerBound rhsLive
        refine .place address.1 env [0] place before placeRoots placeState rfl placePath placeReplay
          (Nat.lt_of_lt_of_le bounded finalGrowth) ?_
        rw [finalPrefix address.1 bounded]
        exact rhsOwner rhsLive)
  have operationSites := rhsSites.emitDef (rfl : emitDef (.bin operation runtimeType loaded.1 value.1 (some origin)) le value.2 = operationRun) finalGrowth finalPrefix
  have finalSites := operationSites.mutationEffect (effect := .store address.1 operationRun.1 (some origin)) trivial rfl (Nat.le_refl _) (fun _ _ => rfl)
  have ledger := ((((placeLedger.retained loadGrowth loadPrefix).retained rhsGrowth rhsPrefix).retained finalGrowth finalPrefix).underRoot placePath).trans
    (((loadLedger.retained rhsGrowth rhsPrefix).retained finalGrowth finalPrefix).trans
      (((rhsLedger.retained finalGrowth finalPrefix).underRoot valuePath).trans (binLedger.trans storeLedger)))
  have retained (old : Nat) (bound : old < upper.vals.size) : rootsAt next.vals old = rootsAt upper.vals old := by
    have placeGrowth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, placeReady.roots.valueSize]
      exact placeAdvance.vals
    have placeBound := Nat.lt_of_lt_of_le bound placeGrowth
    have loadedBound := Nat.lt_of_lt_of_le placeBound loadGrowth
    have rhsBound := Nat.lt_of_lt_of_le loadedBound rhsGrowth
    exact (finalPrefix old rhsBound).trans ((rhsPrefix old loadedBound).trans ((loadPrefix old placeBound).trans (placePrefix old bound)))
  refine ⟨next, completed, retained, (fun expected => occurrence_mutation_transfer loop typed rfl ready retained), ?_, ?_⟩
  · rw [whole]
    exact ledger
  · rw [whole]
    exact finalSites

end Goose.Lower.Validation.SourceReplacementWriterLedger
