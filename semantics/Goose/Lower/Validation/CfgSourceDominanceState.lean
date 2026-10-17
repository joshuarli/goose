import Goose.Lower.Validation.CfgSourceDominanceHelpers

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ImportedState.of_tables {before after : LS} {imports : ImportedValues}
    (checked : ImportedState before imports) (blocks : after.blocks = before.blocks)
    (values : after.vals = before.vals) (current : after.cur = before.cur) :
    ImportedState after imports := by
  refine ⟨checked.certificate.of_blocks blocks, ?_, checked.targets.of_blocks blocks,
    checked.opened.of_state blocks current, ?_⟩
  · simpa only [LS.DenseDefinitions, LS.defs, blocks, values] using checked.definitions
  · intro block bound value imported
    rw [values]
    exact checked.importsBounded block (by simpa only [blocks] using bound) value imported

theorem ImportedState.select {state : LS} {imports : ImportedValues}
    (checked : ImportedState state imports) {block : BlockId} {body : BlockB}
    (row : state.blocks[block]? = some body) (opened : OpenBlock body) (env : LEnv) :
    ImportedState (setCur (some block) env state).2 imports := by
  rw [setCur_run]
  exact ⟨checked.certificate.of_blocks rfl, checked.definitions, checked.targets,
    CurrentOpen.setCur row opened env, checked.importsBounded⟩

theorem ImportedState.newBlock {state : LS} {imports : ImportedValues}
    (checked : ImportedState state imports) (types : List VTy) (values : List ValueId)
    (entry : state.blocks.size = 0 → values = [])
    (bounded : ∀ value ∈ values, value < state.vals.size) (env : LEnv) :
    ImportedState (newBlock types env state).2 (extendImports imports state.blocks.size values) := by
  have valueSize : (Goose.Lower.newBlock types env state).2.vals.size = state.vals.size + types.length :=
    array_size_pushParamTypes types state.vals
  have blockSize : (Goose.Lower.newBlock types env state).2.blocks.size = state.blocks.size + 1 := by
    change (state.blocks.push _).size = _
    simp
  refine ⟨checked.certificate.newBlock checked.targets types values entry bounded env,
    checked.definitions.newBlock (le := env), checked.targets.newBlock types env, checked.opened.newBlock types env, ?_⟩
  intro block bound value imported
  rw [valueSize]
  by_cases fresh : block = state.blocks.size
  · subst block
    have member : value ∈ values := by simpa [extendImports] using imported
    exact Nat.lt_of_lt_of_le (bounded value member) (Nat.le_add_right _ _)
  · have old : block < state.blocks.size := by
      rw [blockSize] at bound
      omega
    have member : value ∈ imports block := by simpa [extendImports, fresh] using imported
    exact Nat.lt_of_lt_of_le (checked.importsBounded block old value member) (Nat.le_add_right _ _)

theorem ImportedState.emitTerm {state : LS} {imports : ImportedValues}
    (checked : ImportedState state imports) (term : Term) (env : LEnv)
    (operands : AvailableValues state imports term.uses)
    (targets : ∀ target ∈ term.successors, target < state.blocks.size)
    (edges : ∀ target ∈ term.successors, AvailableValues state imports (imports target)) :
    ImportedState (emitTerm term env state).2 imports := by
  refine ⟨checked.certificate.emitTerm term env operands
      (fun block current target member value imported => edges target member block current value imported),
    ?_, checked.targets.emitTerm term targets env, currentOpen_emitTerm state term env, ?_⟩
  · cases current : state.cur with
    | none => rw [emitTerm_none term env current]; exact checked.definitions
    | some block =>
      rw [emitTerm_run term env current]
      exact checked.definitions.emitTerm (le := env) (t := term) (checked.opened.bound block current)
  · cases current : state.cur with
    | none => rw [emitTerm_none term env current]; exact checked.importsBounded
    | some block => rw [emitTerm_run term env current]; simpa using checked.importsBounded

theorem newBlock_available_import {state : LS} {imports : ImportedValues} {value : ValueId}
    (types : List VTy) (values : List ValueId) (member : value ∈ values) (env : LEnv) :
    BuilderAvailable (newBlock types env state).2 (extendImports imports state.blocks.size values)
      state.blocks.size value := by
  refine ⟨⟨((List.range types.length).map (state.vals.size + ·)).zip types, #[]⟩, ?_, Or.inl ?_⟩
  · change (state.blocks.push _)[state.blocks.size]? = _
    simp
  · simpa [extendImports] using member

theorem newBlock_available_parameter {state : LS} {imports : ImportedValues} {value : ValueId}
    (types : List VTy) (values : List ValueId)
    (member : value ∈ (newBlock types env state).1.2) :
    BuilderAvailable (newBlock types env state).2 (extendImports imports state.blocks.size values)
      state.blocks.size value := by
  refine ⟨⟨((List.range types.length).map (state.vals.size + ·)).zip types, #[]⟩, ?_, Or.inr ?_⟩
  · change (state.blocks.push _)[state.blocks.size]? = _
    simp
  · have params : (((List.range types.length).map (state.vals.size + ·)).zip types).map Prod.fst =
        (List.range types.length).map (state.vals.size + ·) := List.map_fst_zip (by simp)
    change value ∈ (List.range types.length).map (state.vals.size + ·) at member
    simpa only [cfgBlock, GIR.Block.defs, Array.toList_empty, List.filterMap_nil,
      List.append_nil, params] using member

theorem ImportedState.allocate {state : LS} {imports : ImportedValues}
    (checked : ImportedState state imports) (types : List VTy) (values : List ValueId)
    (entry : state.blocks.size = 0 → values = [])
    (bounded : ∀ value ∈ values, value < state.vals.size) (env : LEnv) :
    SSAResult state (Goose.Lower.newBlock types env state).2 imports
      (extendImports imports state.blocks.size values) [] := by
  have growth : state.Adv (Goose.Lower.newBlock types env state).2 := by
    apply LS.Adv.newBlk
    change state.vals.size ≤ (pushParamTypes types state.vals).size
    rw [array_size_pushParamTypes]
    exact Nat.le_add_right _ _
  have oldImports : ∀ block, block < state.blocks.size →
      extendImports imports state.blocks.size values block = imports block := by
    intro block bound
    simp [extendImports, Nat.ne_of_lt bound]
  refine ⟨checked.newBlock types values entry bounded env, growth, oldImports, ?_, ?_⟩
  · intro saved available block current value member
    exact (available block current value member).of_ext growth.ext oldImports
  · simp [AvailableValues]

theorem ImportedState.allocate_current {state : LS} {imports : ImportedValues}
    (checked : ImportedState state imports) (types : List VTy) (env : LEnv) :
    SSAResult state (Goose.Lower.newBlock types env state).2 imports
      (extendImports imports state.blocks.size (currentValues state imports)) [] := by
  apply checked.allocate types (currentValues state imports) _ _ env
  · intro empty
    cases current : state.cur with
    | none => simp [currentValues, current]
    | some block =>
      have bound := checked.opened.bound block current
      rw [empty] at bound
      exact False.elim (Nat.not_lt_zero block bound)
  · exact currentValues_bounded checked.definitions checked.opened.bound checked.importsBounded

theorem ssa_inScope {loop : Option LoopCtx} {inputs : List ValueId} {outputs : α → List ValueId}
    {action : B α} (scope : ScopeId) (advance : AdvB action)
    (source : SSARun loop inputs outputs action) : SSARun loop inputs outputs (inScope scope action) := by
  intro env before result after run imports checked ready arguments
  obtain ⟨middle, bodyRun, same⟩ := inScope_eq run
  let entered : LS := { before with stack := scope :: before.stack }
  have enteredChecked : ImportedState entered imports := checked.of_tables rfl rfl rfl
  have enteredReady : LoopImportsReady loop entered imports := ⟨ready.bounds, ready.available⟩
  have enteredArguments : AvailableValues entered imports inputs := arguments
  obtain ⟨nextImports, preserved⟩ := source env entered result middle bodyRun imports
    enteredChecked enteredReady enteredArguments
  have afterTables : after.blocks = middle.blocks ∧ after.vals = middle.vals ∧ after.cur = middle.cur := by
    rw [same]
    exact ⟨rfl, rfl, rfl⟩
  refine ⟨nextImports, preserved.checked.of_tables afterTables.1 afterTables.2.1 afterTables.2.2,
    advB_inScope scope advance env before result after run, preserved.imports, ?_, ?_⟩
  · intro values available block current value member
    have lifted : AvailableValues entered imports values := available
    have middleAvailable := preserved.frame values lifted block (afterTables.2.2.symm.trans current) value member
    simpa only [BuilderAvailable, afterTables.1] using middleAvailable
  · intro block current value member
    have middleAvailable := preserved.available block (afterTables.2.2.symm.trans current) value member
    simpa only [BuilderAvailable, afterTables.1] using middleAvailable

end Goose.Lower.Validation
