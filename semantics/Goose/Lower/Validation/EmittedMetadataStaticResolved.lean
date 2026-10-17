import Goose.Lower.Validation.EmittedMetadataStaticTables

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem EmittedBodyResolved.of_transport {module : Core.Module} {before after : LS}
    (checked : EmittedBodyResolved module before)
    (parameters : ∀ block ∈ after.blocks.toList, ∀ parameter ∈ block.params,
      (∃ old ∈ before.blocks.toList, parameter ∈ old.params) ∨ EmittedVTyResolved module parameter.2)
    (instructions : ∀ inst ∈ after.insts, inst ∈ before.insts ∨ EmittedAnnotationResolved module inst) :
    EmittedBodyResolved module after := by
  constructor
  · intro block member parameter atParameter
    rcases parameters block member parameter atParameter with ⟨old, oldMember, oldParameter⟩ | fresh
    · exact checked.parameters old oldMember parameter oldParameter
    · exact fresh
  · intro inst member
    rcases instructions inst member with old | fresh
    · exact checked.annotations inst old
    · exact fresh

theorem EmittedBodyResolved.of_blocks_eq {module : Core.Module} {before after : LS}
    (checked : EmittedBodyResolved module before) (same : after.blocks = before.blocks) :
    EmittedBodyResolved module after := by
  constructor
  · simpa only [same] using checked.parameters
  · simpa only [LS.insts, same] using checked.annotations

theorem EmittedBodyResolved.appendInst {module : Core.Module} {before : LS}
    (checked : EmittedBodyResolved module before) (block : BlockId) (inst : Inst)
    (annotation : EmittedAnnotationResolved module inst) :
    EmittedBodyResolved module (before.appendInst block inst) := by
  apply checked.of_transport
  · intro body member parameter atParameter
    obtain ⟨index, lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    change (before.blocks.modify block fun b => { b with insts := b.insts.push inst })[index]? = some body at lookup
    rw [Array.getElem?_modify] at lookup
    by_cases same : block = index
    · simp only [same, ↓reduceIte] at lookup
      cases old : before.blocks[index]? with
      | none => simp [old] at lookup
      | some prior =>
        simp only [old, Option.map_some, Option.some.injEq] at lookup
        subst body
        exact Or.inl ⟨prior, Array.mem_toList_iff.mpr (Array.mem_of_getElem? old), atParameter⟩
    · simp only [same, ↓reduceIte] at lookup
      exact Or.inl ⟨body, Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup), atParameter⟩
  · intro next member
    rcases insts_appendInst_member member with old | rfl
    · exact Or.inl old
    · exact Or.inr annotation

structure EmittedResolvedState (module : Core.Module) (state : LS) : Prop
    extends EmittedBodyResolved module state where
  values : EmittedResolvedValues module state

def EmittedResolvedRun (module : Core.Module) (le : LEnv) (action : B α) : Prop :=
  ∀ before result after, action le before = (result, after) →
    EmittedResolvedState module before → EmittedResolvedState module after

theorem EmittedResolvedRun.pure (module : Core.Module) (le : LEnv) (value : α) :
    EmittedResolvedRun module le (pure value) := by
  intro before result after run checked
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact checked

theorem EmittedResolvedRun.bind {module : Core.Module} {le : LEnv}
    {action : B α} {next : α → B β} (first : EmittedResolvedRun module le action)
    (second : ∀ value, EmittedResolvedRun module le (next value)) :
    EmittedResolvedRun module le (action >>= next) := by
  intro before result after run checked
  obtain ⟨value, middle, firstRun, secondRun⟩ := bind_eq.mp run
  exact second value _ _ _ secondRun (first _ _ _ firstRun checked)

theorem EmittedResolvedState.initState (module : Core.Module) : EmittedResolvedState module initState := by
  exact ⟨(EmittedStatic.initState module).resolved, (EmittedStaticState.initState module).values⟩

theorem EmittedResolvedState.valTy {module : Core.Module} {state : LS}
    (checked : EmittedResolvedState module state) (le : LEnv) (value : ValueId) :
    EmittedVTyResolved module (Goose.Lower.valTy value le state).1 := by
  unfold Goose.Lower.valTy
  simp only [bind_run, get_apply]
  cases row : state.vals[value]? with
  | none => rfl
  | some found =>
    cases found with
    | none => rfl
    | some type => exact checked.values value type row

theorem EmittedResolvedRun.of_unchanged {module : Core.Module} {le : LEnv} {action : B α}
    (blocks : ∀ before, (action le before).2.blocks = before.blocks)
    (values : ∀ before, (action le before).2.vals = before.vals) :
    EmittedResolvedRun module le action := by
  intro before result after run checked
  have sameBlocks := blocks before
  have sameValues := values before
  rw [run] at sameBlocks sameValues
  refine ⟨checked.toEmittedBodyResolved.of_blocks_eq sameBlocks, ?_⟩
  change after.vals = before.vals at sameValues
  intro value type row
  exact checked.values value type (sameValues ▸ row)

theorem resolved_emitDef {module : Core.Module} {le : LEnv}
    (tables : EmittedStaticTables module le) (op : Op)
    (annotation : ∀ value, EmittedAnnotationResolved module (.def value op)) :
    EmittedResolvedRun module le (emitDef op) := by
  intro before result after run checked
  constructor
  · cases live : before.cur with
    | none =>
      rw [emitDef_none op le live] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      exact checked.toEmittedBodyResolved
    | some block =>
      rw [emitDef_run op le live] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      exact (checked.toEmittedBodyResolved.appendInst block (.def before.vals.size op) (annotation _)).of_blocks_eq rfl
  ·
    cases live : before.cur with
    | none =>
      rw [emitDef_none op le live] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      exact checked.values
    | some block =>
      rw [emitDef_run op le live] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      intro value type row
      change (before.vals.push (some ((op.resultTy (tyEnv le before)).toOption.getD (.data .unit))))[value]? = some (some type) at row
      by_cases fresh : value = before.vals.size
      · subst value
        simp only [Array.getElem?_push_size, Option.some.injEq] at row
        subst type
        cases output : op.resultTy (tyEnv le before) with
        | error _ => rfl
        | ok outputType =>
          exact op_resultTy_resolved (tables.environment checked.values) op annotation output
      · have old : before.vals[value]? = some (some type) := by
          simpa only [Array.getElem?_push, fresh, ↓reduceIte] using row
        exact checked.values value type old
  

theorem resolved_emitEffect {module : Core.Module} {le : LEnv} (effect : Effect) :
    EmittedResolvedRun module le (emitEffect effect) := by
  intro before result after run checked
  cases live : before.cur with
  | none =>
    rw [emitEffect_none effect le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitEffect_run effect le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨checked.toEmittedBodyResolved.appendInst block (.eff effect) trivial, checked.values⟩

theorem resolved_emitTerm {module : Core.Module} {le : LEnv} (term : Term) :
    EmittedResolvedRun module le (emitTerm term) := by
  intro before result after run checked
  cases live : before.cur with
  | none =>
    rw [emitTerm_none term le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitTerm_run term le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨(checked.toEmittedBodyResolved.appendInst block (.term term) trivial).of_blocks_eq rfl, checked.values⟩

theorem resolved_patchTerm {module : Core.Module} {le : LEnv} (block : BlockId) (term : Term) :
    EmittedResolvedRun module le (patchTerm block term) := by
  intro before result after run checked
  rw [patchTerm_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨checked.toEmittedBodyResolved.appendInst block (.term term) trivial, checked.values⟩

theorem resolved_newBlock {module : Core.Module} {le : LEnv} (types : List VTy)
    (resolved : ∀ type ∈ types, EmittedVTyResolved module type) :
    EmittedResolvedRun module le (newBlock types) := by
  intro before result after run checked
  rw [newBlock_run_general] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  refine ⟨?_, checked.values.pushTypes types before resolved⟩
  apply checked.toEmittedBodyResolved.of_transport
  · intro block member parameter parameterAt
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact Or.inl ⟨block, old, parameterAt⟩
    · exact Or.inr (resolved parameter.2 (List.of_mem_zip parameterAt).2)
  · intro inst member
    exact Or.inl (by simpa [LS.insts] using member)

theorem resolved_get (module : Core.Module) (le : LEnv) : EmittedResolvedRun module le (get : B LS) :=
  EmittedResolvedRun.of_unchanged (fun _ => rfl) (fun _ => rfl)

theorem resolved_read (module : Core.Module) (le : LEnv) : EmittedResolvedRun module le (read : B LEnv) :=
  EmittedResolvedRun.of_unchanged (fun _ => rfl) (fun _ => rfl)

theorem resolved_valTy (module : Core.Module) (le : LEnv) (value : ValueId) :
    EmittedResolvedRun module le (valTy value) :=
  EmittedResolvedRun.of_unchanged (fun before => by rw [valTy_run]) (fun before => by rw [valTy_run])

theorem resolved_curBlock (module : Core.Module) (le : LEnv) : EmittedResolvedRun module le curBlock :=
  EmittedResolvedRun.of_unchanged (fun before => by rw [curBlock_run]) (fun before => by rw [curBlock_run])

theorem resolved_setCur (module : Core.Module) (le : LEnv) (block : Option BlockId) :
    EmittedResolvedRun module le (setCur block) :=
  EmittedResolvedRun.of_unchanged (fun before => by rw [setCur_run]) (fun before => by rw [setCur_run])

theorem resolved_pushScope (module : Core.Module) (le : LEnv) (scope : ScopeId) :
    EmittedResolvedRun module le (pushScope scope) :=
  EmittedResolvedRun.of_unchanged (fun before => by rw [pushScope_run]) (fun before => by rw [pushScope_run])

theorem resolved_popScope (module : Core.Module) (le : LEnv) : EmittedResolvedRun module le popScope :=
  EmittedResolvedRun.of_unchanged (fun before => by rw [popScope_run]) (fun before => by rw [popScope_run])

end Goose.Lower.Validation
