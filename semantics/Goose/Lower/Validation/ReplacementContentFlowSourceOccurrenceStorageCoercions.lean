import Goose.Lower.Validation.SummaryPreservationStoppedCoercions
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceMutationsActions
import Goose.Lower.Validation.SummaryPreservationCoercions
import Goose.Lower.Validation.EmittedTypingOperations

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

private theorem coercion_cases (target : Ty) (value : ValueId) (org : OriginId) (le : LEnv) (state : LS) :
    coerceTo target value org le state = (value, state) ∨
    coerceTo target value org le state = emitDef (.refFreeze value) le state ∨
    (∃ element, (valTy value le state).1 = .data (.slice .mutable element) ∧
      coerceTo target value org le state =
        let view := emitDef (.sliceView value) le state
        emitDef (.viewSlice .readOnly view.1 .omitted .omitted (some org)) le view.2) := by
  simp only [coerceTo, bind_run, valTy_run]
  generalize valueTypeRow : (valTy value le state).1 = valueType
  cases target <;> cases valueType <;> try exact Or.inl rfl
  case ref.data targetMutability target actualType =>
    cases targetMutability <;> cases actualType <;> try exact Or.inl rfl
    rename_i actualMutability actualTarget
    cases actualMutability <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
  case ref.view targetMutability target viewMutability element =>
    cases targetMutability <;> exact Or.inl rfl
  case slice.view targetMutability element viewMutability viewElement =>
    cases targetMutability <;> exact Or.inl rfl
  case slice.data targetMutability element actualType =>
    cases targetMutability <;> cases actualType <;> try exact Or.inl rfl
    rename_i actualMutability actualElement
    cases actualMutability <;> first | exact Or.inl rfl | exact Or.inr (Or.inr ⟨actualElement, rfl, rfl⟩)

namespace ReplayBuilder

variable {env : PEnv} {root siteRoot node : DemandNode} {targets : List BlockId}
  {module : GIR.Module} {results : Array (List RootRef)} {types : Array (Option VTy)} {func : Func}
  {effect : Core.Eff} {le : LEnv} {scopeCount : Nat} {slots : Array (List RootRef)}
  {state : LS} {upper : Prov} {block : BlockId} {value : ValueId}
  {start finish : RState} {sourceRoots : List RootRef} {path : List Nat}

private theorem occurrenceRelayDef (op : Op)
    (ready : ReplayBuilder module results types func effect le scopeCount slots state upper)
    (sites : OccurrenceSitesBuilder env siteRoot targets le state func types upper)
    (source : DemandNodeAt root path node) (replay : SourceNodeRoots env.access node start sourceRoots finish)
    (current : state.cur = some block) (valueBound : value < state.vals.size)
    (refined : GIR.RootsRefine func (rootsAt upper.vals value) sourceRoots)
    (uses : ∀ operand ∈ op.uses, operand < state.vals.size)
    (origin : ∀ org, op.origin = some org → org < le.mod.origins.size)
    (symbols : Op.SymbolRefsValid le op)
    (relay : rootsOfDef results types func upper state.vals.size op = rootsAt upper.vals value)
    (neutral : func.effectStep module types upper {} (.def state.vals.size op) = {})
    (operands : ∀ result operand, operand ∈ GIR.ReplacementContentFlow.Model.accessOperands (.def result op) → operand = value)
    (noLoad : ∀ address, op ≠ .load address) (noCall : ∀ fn args origin, op ≠ .call fn args origin)
    (noReferences : ∀ result, ∀ operand ∈ GIR.ReplacementContentFlow.Model.accessOperands (.def result op),
      ∀ mutability payload, types[operand]? ≠ some (some (.data (.ref mutability payload)))) :
    ∃ next, ReplayBuilder module results types func effect le scopeCount slots (emitDef op le state).2 next ∧
      GIR.RootsRefine func (rootsAt next.vals (emitDef op le state).1) sourceRoots ∧
      (emitDef op le state).2.cur = some block ∧
      (emitDef op le state).1 < (emitDef op le state).2.vals.size ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env root func types next state (emitDef op le state).2 ∧
      OccurrenceSitesBuilder env siteRoot targets le (emitDef op le state).2 func types next := by
  obtain ⟨next, nextRoots, nextEffects, nextValue, nextSlots, nextSymbols, nextCurrent, nextBlock,
    nextBound, retained⟩ := emitDef_relay_refined_witness_growth op ready.symbols current
      (ready.current block current) ready.roots ready.effects refined uses origin symbols relay neutral
  have growth : upper.vals.size ≤ next.vals.size := by
    rw [ready.roots.valueSize, nextRoots.valueSize]
    exact (advB_emitDef op le state _ _ rfl).vals
  have nextReady : ReplayBuilder module results types func effect le scopeCount slots (emitDef op le state).2 next :=
    ⟨nextRoots, nextEffects, nextSymbols, fun b row => by rw [nextCurrent] at row; cases row; exact nextBlock,
      nextSlots.trans ready.slotsEq,
      ready.recipes.prefix (recipesUnchangedB_emitDef op le state) retained growth⟩
  have oldBound : value < upper.vals.size := ready.roots.valueSize ▸ valueBound
  have operand : OperandOccurrence env root func next value := by
    refine ⟨path, node, start, sourceRoots, finish, source, replay, Nat.lt_of_lt_of_le oldBound growth, ?_⟩
    rw [retained value oldBound]
    exact refined
  have emitted : OccurrenceLedger env root func types next state (emitDef op le state).2 := by
    apply occurrence_emitDef_live rfl
    intro _
    refine InstructionOccurrences.of_def ?_ noLoad noCall (InstructionOccurrences.no_references (noReferences _))
    intro used member
    rw [operands _ used member]
    exact operand
  exact ⟨next, nextReady, nextValue, nextCurrent, nextBound, retained, emitted, sites.emitDef rfl growth retained⟩

theorem occurrenceCoerceTo (target : Ty) (origin : OriginId)
    (ready : ReplayBuilder module results types func effect le scopeCount slots state upper)
    (sites : OccurrenceSitesBuilder env siteRoot targets le state func types upper)
    (source : DemandNodeAt root path node) (replay : SourceNodeRoots env.access node start sourceRoots finish)
    (current : state.cur = some block) (valueBound : value < state.vals.size)
    (refined : GIR.RootsRefine func (rootsAt upper.vals value) sourceRoots)
    (originBound : origin < le.mod.origins.size)
    (native : NativeRows types (coerceTo target value origin le state).2) :
    ∃ next, ReplayBuilder module results types func effect le scopeCount slots (coerceTo target value origin le state).2 next ∧
      GIR.RootsRefine func (rootsAt next.vals (coerceTo target value origin le state).1) sourceRoots ∧
      (coerceTo target value origin le state).2.cur = some block ∧
      (coerceTo target value origin le state).1 < (coerceTo target value origin le state).2.vals.size ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env root func types next state (coerceTo target value origin le state).2 ∧
      OccurrenceSitesBuilder env siteRoot targets le (coerceTo target value origin le state).2 func types next := by
  rcases coercion_cases target value origin le state with same | freeze | slice
  · rw [same]
    exact ⟨upper, ready, refined, current, valueBound, fun _ _ => rfl, .refl _ _, sites⟩
  · rw [freeze]
    exact occurrenceRelayDef (.refFreeze value) ready sites source replay current valueBound refined
      (by simpa [Op.uses] using valueBound) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid]) rfl rfl
      (by intro result operand member; simp [GIR.ReplacementContentFlow.Model.accessOperands] at member)
      (by intro address same; cases same) (by intro fn args origin same; cases same)
      (by intro result operand member; simp [GIR.ReplacementContentFlow.Model.accessOperands] at member)
  · obtain ⟨element, sourceType, slice⟩ := slice
    have sourceRow := emitted_valTy_nonunit (by intro equality; cases equality) sourceType
    have beforeNative := native.of_prefix (types_coerceTo target value origin le state _ _ rfl)
    have sourceNative := beforeNative value _ sourceRow
    have viewNative : NativeRows types (emitDef (.sliceView value) le state).2 := by
      rw [slice] at native
      exact native.of_prefix (types_emitDef _ le _ _ _ rfl)
    have viewType : (Op.sliceView value).resultTy (tyEnv le state) = .ok (.view .mutable element) := by
      simp [Op.resultTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, sourceRow, pure, Except.pure, bind, Except.bind]
    have viewRow : types[(Goose.Lower.emitDef (.sliceView value) le state).1]? = some (some (.view .mutable element)) :=
      viewNative _ _ (emitDef_recorded current viewType).2.2.1
    rw [slice]
    obtain ⟨middle, middleReady, middleValue, middleCurrent, middleBound, middlePrefix, middleLedger, middleSites⟩ :=
      occurrenceRelayDef (.sliceView value) ready sites source replay current valueBound refined
        (by simpa [Op.uses] using valueBound) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid]) rfl rfl
        (by intro result operand member; simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] using member)
        (by intro address same; cases same) (by intro fn args origin same; cases same)
        (by intro result operand member mutability payload reference
            have same : operand = value := by simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] using member
            subst operand
            simp [sourceNative] at reference)
    obtain ⟨next, nextReady, nextValue, nextCurrent, nextBound, nextPrefix, nextLedger, nextSites⟩ :=
      occurrenceRelayDef (.viewSlice .readOnly (emitDef (.sliceView value) le state).1 .omitted .omitted (some origin))
        middleReady middleSites source replay middleCurrent middleBound middleValue
        (by simpa [Op.uses, Bnd.uses] using middleBound) (by simpa [Op.origin] using originBound)
        (by simp [Op.SymbolRefsValid]) rfl rfl
        (by intro result operand member; simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, Bnd.uses] using member)
        (by intro address same; cases same) (by intro fn args origin same; cases same)
        (by intro result operand member mutability payload reference
            have same : operand = (emitDef (.sliceView value) le state).1 := by
              simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, Bnd.uses] using member
            subst operand
            rw [viewRow] at reference
            cases reference)
    have growth : middle.vals.size ≤ next.vals.size := by
      rw [middleReady.roots.valueSize, nextReady.roots.valueSize]
      exact (advB_emitDef _ _ _ _ _ rfl).vals
    refine ⟨next, nextReady, nextValue, nextCurrent, nextBound, ?_,
      (middleLedger.retained growth nextPrefix).trans nextLedger, nextSites⟩
    intro old bound
    have middleGrowth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, middleReady.roots.valueSize]
      exact (advB_emitDef _ _ _ _ _ rfl).vals
    exact (nextPrefix old (Nat.lt_of_lt_of_le bound middleGrowth)).trans (middlePrefix old bound)

theorem occurrenceCoerceSlot (slotId : SlotId) (origin : OriginId)
    (ready : ReplayBuilder module results types func effect le scopeCount slots state upper)
    (sites : OccurrenceSitesBuilder env siteRoot targets le state func types upper)
    (source : DemandNodeAt root path node) (replay : SourceNodeRoots env.access node start sourceRoots finish)
    (current : state.cur = some block) (valueBound : value < state.vals.size)
    (refined : GIR.RootsRefine func (rootsAt upper.vals value) sourceRoots)
    (originBound : origin < le.mod.origins.size)
    (native : NativeRows types (coerceSlot slotId value origin le state).2) :
    ∃ next, ReplayBuilder module results types func effect le scopeCount slots (coerceSlot slotId value origin le state).2 next ∧
      GIR.RootsRefine func (rootsAt next.vals (coerceSlot slotId value origin le state).1) sourceRoots ∧
      (coerceSlot slotId value origin le state).2.cur = some block ∧
      (coerceSlot slotId value origin le state).1 < (coerceSlot slotId value origin le state).2.vals.size ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env root func types next state (coerceSlot slotId value origin le state).2 ∧
      OccurrenceSitesBuilder env siteRoot targets le (coerceSlot slotId value origin le state).2 func types next := by
  simp only [coerceSlot, bind_run, read_apply]
  cases row : le.slots[slotId]? with
  | none => exact ⟨upper, ready, refined, current, valueBound, fun _ _ => rfl, .refl _ _, sites⟩
  | some destination => exact occurrenceCoerceTo destination.ty origin ready sites source replay current valueBound refined originBound (by simpa [coerceSlot, bind_run, read_apply, row] using native)

theorem occurrenceCoerceResult (origin : OriginId)
    (ready : ReplayBuilder module results types func effect le scopeCount slots state upper)
    (sites : OccurrenceSitesBuilder env siteRoot targets le state func types upper)
    (source : DemandNodeAt root path node) (replay : SourceNodeRoots env.access node start sourceRoots finish)
    (current : state.cur = some block) (valueBound : value < state.vals.size)
    (refined : GIR.RootsRefine func (rootsAt upper.vals value) sourceRoots)
    (originBound : origin < le.mod.origins.size)
    (native : NativeRows types (coerceResult value origin le state).2) :
    ∃ next, ReplayBuilder module results types func effect le scopeCount slots (coerceResult value origin le state).2 next ∧
      GIR.RootsRefine func (rootsAt next.vals (coerceResult value origin le state).1) sourceRoots ∧
      (coerceResult value origin le state).2.cur = some block ∧
      (coerceResult value origin le state).1 < (coerceResult value origin le state).2.vals.size ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env root func types next state (coerceResult value origin le state).2 ∧
      OccurrenceSitesBuilder env siteRoot targets le (coerceResult value origin le state).2 func types next := by
  simp only [coerceResult, bind_run, read_apply]
  cases row : le.results.head? with
  | none => exact ⟨upper, ready, refined, current, valueBound, fun _ _ => rfl, .refl _ _, sites⟩
  | some destination => exact occurrenceCoerceTo destination origin ready sites source replay current valueBound refined originBound (by simpa [coerceResult, bind_run, read_apply, row] using native)

end ReplayBuilder
end Goose.Lower.Validation.ReplacementContentFlowSource
