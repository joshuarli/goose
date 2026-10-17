import Goose.Lower.Validation.SourceValueTypeShapesOperations
import Goose.Lower.Validation.EmittedMetadataStaticResolved

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

structure ShapeBody (module : Core.Module) (state : LS) : Prop where
  parameters : ∀ block ∈ state.blocks.toList, ∀ parameter ∈ block.params, ValueTypeShape parameter.2
  annotations : ∀ inst ∈ state.insts, ShapeAnnotation inst

structure ShapeTables (module : Core.Module) (le : LEnv) : Prop where
  slots : ∀ (index : Nat) (descriptor : Slot), le.slots[index]? = some descriptor → descriptor.ty.paramOk = true
  globals : ∀ (index : Nat) (type : Ty) (kind : VarKind), le.globals[index]? = some (type, kind) → type.storable = true
  signatures : ∀ (index : Nat) (params results : List Ty), le.sigs[index]? = some (params, results) →
    ∀ type ∈ results, type.storable = true
  fields : ∀ (index : Nat) (descriptor : StructDef), le.mod.structs[index]? = some descriptor →
    ∀ (fieldIndex : Nat) (field : StructField), descriptor.fields[fieldIndex]? = some field → field.ty.flat = true

theorem ShapeTables.environment {module : Core.Module} {le : LEnv} {state : LS}
    (tables : ShapeTables module le) (values : ValueTypeShapes state.vals) : ShapeTyEnv (tyEnv le state) :=
  ⟨values, tables.slots, tables.globals, tables.signatures, tables.fields⟩

theorem shapedValues_push {state : LS} (checked : ValueTypeShapes state.vals) (type : VTy)
    (shape : ValueTypeShape type) : ValueTypeShapes (state.vals.push (some type)) := by
  intro value found row
  by_cases fresh : value = state.vals.size
  · subst value
    simp only [Array.getElem?_push_size, Option.some.injEq] at row
    cases row
    exact shape
  · exact checked value found (by simpa only [Array.getElem?_push, fresh, ↓reduceIte] using row)

theorem shapedValues_pushTypes (types : List VTy) (state : LS)
    (checked : ValueTypeShapes state.vals) (shape : ∀ type ∈ types, ValueTypeShape type) :
    ValueTypeShapes (pushParamTypes types state.vals) := by
  induction types generalizing state with
  | nil => exact checked
  | cons type types ih =>
    exact ih {state with vals := state.vals.push (some type)}
      (shapedValues_push checked type (shape type (by simp))) (fun item member => shape item (by simp [member]))

theorem ShapeBody.of_transport {module : Core.Module} {before after : LS}
    (checked : ShapeBody module before)
    (parameters : ∀ block ∈ after.blocks.toList, ∀ parameter ∈ block.params,
      (∃ old ∈ before.blocks.toList, parameter ∈ old.params) ∨ ValueTypeShape parameter.2)
    (instructions : ∀ inst ∈ after.insts, inst ∈ before.insts ∨ ShapeAnnotation inst) :
    ShapeBody module after := by
  constructor
  · intro block member parameter atParameter
    rcases parameters block member parameter atParameter with ⟨old, oldMember, oldParameter⟩ | fresh
    · exact checked.parameters old oldMember parameter oldParameter
    · exact fresh
  · intro inst member
    rcases instructions inst member with old | fresh
    · exact checked.annotations inst old
    · exact fresh

theorem ShapeBody.of_blocks_eq {module : Core.Module} {before after : LS}
    (checked : ShapeBody module before) (same : after.blocks = before.blocks) :
    ShapeBody module after := by
  constructor
  · simpa only [same] using checked.parameters
  · simpa only [LS.insts, same] using checked.annotations

theorem ShapeBody.appendInst {module : Core.Module} {before : LS}
    (checked : ShapeBody module before) (block : BlockId) (inst : Inst)
    (annotation : ShapeAnnotation inst) :
    ShapeBody module (before.appendInst block inst) := by
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

structure EmittedShapeState (module : Core.Module) (state : LS) : Prop
    extends ShapeBody module state where
  values : ValueTypeShapes state.vals

def EmittedShapeRun (module : Core.Module) (le : LEnv) (action : B α) : Prop :=
  ∀ before result after, action le before = (result, after) →
    EmittedShapeState module before → EmittedShapeState module after

theorem EmittedShapeRun.pure (module : Core.Module) (le : LEnv) (value : α) :
    EmittedShapeRun module le (pure value) := by
  intro before result after run checked
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact checked

theorem EmittedShapeRun.bind {module : Core.Module} {le : LEnv}
    {action : B α} {next : α → B β} (first : EmittedShapeRun module le action)
    (second : ∀ value, EmittedShapeRun module le (next value)) :
    EmittedShapeRun module le (action >>= next) := by
  intro before result after run checked
  obtain ⟨value, middle, firstRun, secondRun⟩ := bind_eq.mp run
  exact second value _ _ _ secondRun (first _ _ _ firstRun checked)

theorem EmittedShapeState.initState (module : Core.Module) : EmittedShapeState module initState := by
  exact ⟨⟨by simp [Goose.Lower.initState], by simp [LS.insts, Goose.Lower.initState]⟩, by simp [ValueTypeShapes, Goose.Lower.initState]⟩

theorem EmittedShapeState.valTy {module : Core.Module} {state : LS}
    (checked : EmittedShapeState module state) (le : LEnv) (value : ValueId) :
    ValueTypeShape (Goose.Lower.valTy value le state).1 := by
  unfold Goose.Lower.valTy
  simp only [bind_run, get_apply]
  cases row : state.vals[value]? with
  | none => simp [pure_run, ValueTypeShape, DataTypeShape]
  | some found =>
    cases found with
    | none => simp [pure_run, ValueTypeShape, DataTypeShape]
    | some type => exact checked.values value type row

theorem EmittedShapeRun.of_unchanged {module : Core.Module} {le : LEnv} {action : B α}
    (blocks : ∀ before, (action le before).2.blocks = before.blocks)
    (values : ∀ before, (action le before).2.vals = before.vals) :
    EmittedShapeRun module le action := by
  intro before result after run checked
  have sameBlocks := blocks before
  have sameValues := values before
  rw [run] at sameBlocks sameValues
  refine ⟨checked.toShapeBody.of_blocks_eq sameBlocks, ?_⟩
  change after.vals = before.vals at sameValues
  intro value type row
  exact checked.values value type (sameValues ▸ row)

theorem shaped_emitDef {module : Core.Module} {le : LEnv}
    (tables : ShapeTables module le) (op : Op)
    (annotation : ∀ value, ShapeAnnotation (.def value op)) :
    EmittedShapeRun module le (emitDef op) := by
  intro before result after run checked
  constructor
  · cases live : before.cur with
    | none =>
      rw [emitDef_none op le live] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      exact checked.toShapeBody
    | some block =>
      rw [emitDef_run op le live] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      exact (checked.toShapeBody.appendInst block (.def before.vals.size op) (annotation _)).of_blocks_eq rfl
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
        | error _ => simp [output, Except.toOption, ValueTypeShape, DataTypeShape]
        | ok outputType =>
          exact op_resultTy_shape (tables.environment checked.values) op annotation output
      · have old : before.vals[value]? = some (some type) := by
          simpa only [Array.getElem?_push, fresh, ↓reduceIte] using row
        exact checked.values value type old


theorem shaped_emitEffect {module : Core.Module} {le : LEnv} (effect : Effect) :
    EmittedShapeRun module le (emitEffect effect) := by
  intro before result after run checked
  cases live : before.cur with
  | none =>
    rw [emitEffect_none effect le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitEffect_run effect le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨checked.toShapeBody.appendInst block (.eff effect) trivial, checked.values⟩

theorem shaped_emitTerm {module : Core.Module} {le : LEnv} (term : Term) :
    EmittedShapeRun module le (emitTerm term) := by
  intro before result after run checked
  cases live : before.cur with
  | none =>
    rw [emitTerm_none term le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitTerm_run term le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨(checked.toShapeBody.appendInst block (.term term) trivial).of_blocks_eq rfl, checked.values⟩

theorem shaped_patchTerm {module : Core.Module} {le : LEnv} (block : BlockId) (term : Term) :
    EmittedShapeRun module le (patchTerm block term) := by
  intro before result after run checked
  rw [patchTerm_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨checked.toShapeBody.appendInst block (.term term) trivial, checked.values⟩

theorem shaped_newBlock {module : Core.Module} {le : LEnv} (types : List VTy)
    (resolved : ∀ type ∈ types, ValueTypeShape type) :
    EmittedShapeRun module le (newBlock types) := by
  intro before result after run checked
  rw [newBlock_run_general] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  refine ⟨?_, shapedValues_pushTypes types before checked.values resolved⟩
  apply checked.toShapeBody.of_transport
  · intro block member parameter parameterAt
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact Or.inl ⟨block, old, parameterAt⟩
    · exact Or.inr (resolved parameter.2 (List.of_mem_zip parameterAt).2)
  · intro inst member
    exact Or.inl (by simpa [LS.insts] using member)

theorem shaped_get (module : Core.Module) (le : LEnv) : EmittedShapeRun module le (get : B LS) :=
  EmittedShapeRun.of_unchanged (fun _ => rfl) (fun _ => rfl)

theorem shaped_read (module : Core.Module) (le : LEnv) : EmittedShapeRun module le (read : B LEnv) :=
  EmittedShapeRun.of_unchanged (fun _ => rfl) (fun _ => rfl)

theorem shaped_valTy (module : Core.Module) (le : LEnv) (value : ValueId) :
    EmittedShapeRun module le (valTy value) :=
  EmittedShapeRun.of_unchanged (fun before => by rw [valTy_run]) (fun before => by rw [valTy_run])

theorem shaped_curBlock (module : Core.Module) (le : LEnv) : EmittedShapeRun module le curBlock :=
  EmittedShapeRun.of_unchanged (fun before => by rw [curBlock_run]) (fun before => by rw [curBlock_run])

theorem shaped_setCur (module : Core.Module) (le : LEnv) (block : Option BlockId) :
    EmittedShapeRun module le (setCur block) :=
  EmittedShapeRun.of_unchanged (fun before => by rw [setCur_run]) (fun before => by rw [setCur_run])

theorem shaped_pushScope (module : Core.Module) (le : LEnv) (scope : ScopeId) :
    EmittedShapeRun module le (pushScope scope) :=
  EmittedShapeRun.of_unchanged (fun before => by rw [pushScope_run]) (fun before => by rw [pushScope_run])

theorem shaped_popScope (module : Core.Module) (le : LEnv) : EmittedShapeRun module le popScope :=
  EmittedShapeRun.of_unchanged (fun before => by rw [popScope_run]) (fun before => by rw [popScope_run])

end Goose.Lower.Validation
