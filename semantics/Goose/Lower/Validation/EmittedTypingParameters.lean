import Goose.Lower.Validation.EmittedTypingBuilder

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def EmittedParametersTyped (state : LS) : Prop :=
  ∀ (block : BlockId) (body : BlockB), state.blocks[block]? = some body → ∀ (value : ValueId) (type : VTy), (value, type) ∈ body.params →
    state.vals[value]? = some (some type)

theorem EmittedParametersTyped.modify {before after : LS} (typed : EmittedParametersTyped before)
    (types : TypePrefix before after) (index : BlockId) (update : BlockB → BlockB)
    (parameters : ∀ body, (update body).params = body.params)
    (blocks : after.blocks = before.blocks.modify index update) : EmittedParametersTyped after := by
  intro block body row value type member
  rw [blocks, Array.getElem?_modify] at row
  by_cases same : index = block
  · simp only [same, ↓reduceIte] at row
    cases previous : before.blocks[block]? with
    | none => simp [previous] at row
    | some old =>
      simp only [previous, Option.map_some, Option.some.injEq] at row
      subst body
      rw [parameters] at member
      exact types value type (typed block old previous value type member)
  · simp only [same, ↓reduceIte] at row
    exact types value type (typed block body row value type member)

theorem emitted_parameter_allocated (types : List VTy) (values : Array (Option VTy))
    {value : ValueId} {type : VTy} (member : (value, type) ∈ (paramIds types values).zip types) :
    (pushParamTypes types values)[value]? = some (some type) := by
  obtain ⟨index, row⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨idRow, typeRow⟩ := List.getElem?_zip_eq_some.mp row
  have bound := (List.getElem?_eq_some_iff.mp typeRow).1
  have id : values.size + index = value := by
    simpa only [paramIds, List.getElem?_map, List.getElem?_range bound, Option.map_some, Option.some.injEq] using idRow
  rw [← id, pushParamTypes_lookup, typeRow]
  rfl

theorem EmittedParametersTyped.newBlock {before : LS} (typed : EmittedParametersTyped before)
    (le : LEnv) (types : List VTy) : EmittedParametersTyped (Goose.Lower.newBlock types le before).2 := by
  intro block body row value type member
  rw [newBlock_run_general] at row ⊢
  simp only [Array.getElem?_push] at row
  by_cases fresh : block = before.blocks.size
  · simp only [fresh, ↓reduceIte, Option.some.injEq] at row
    subst body
    exact emitted_parameter_allocated types before.vals member
  · simp only [fresh, ↓reduceIte] at row
    exact (emittedTypePrefix_newBlock types le before).typed value type (typed block body row value type member)


theorem EmittedParametersTyped.emitDef {before : LS} (typed : EmittedParametersTyped before)
    (le : LEnv) (op : Op) : EmittedParametersTyped (Goose.Lower.emitDef op le before).2 := by
  cases live : before.cur with
  | none => rw [emitDef_none op le live]; exact typed
  | some block =>
    apply typed.modify (types_emitDef op le before _ _ rfl) block
      (fun body => { body with insts := body.insts.push (.def before.vals.size op) }) (fun _ => rfl)
    exact congrArg (fun pair => pair.2.blocks) (emitDef_run op le live)

theorem EmittedParametersTyped.emitEffect {before : LS} (typed : EmittedParametersTyped before)
    (le : LEnv) (effect : Effect) : EmittedParametersTyped (Goose.Lower.emitEffect effect le before).2 := by
  cases live : before.cur with
  | none => rw [emitEffect_none effect le live]; exact typed
  | some block =>
    apply typed.modify (types_emitEffect effect le before _ _ rfl) block
      (fun body => { body with insts := body.insts.push (.eff effect) }) (fun _ => rfl)
    exact congrArg (fun pair => pair.2.blocks) (emitEffect_run effect le live)

theorem EmittedParametersTyped.emitTerm {before : LS} (typed : EmittedParametersTyped before)
    (le : LEnv) (term : Term) : EmittedParametersTyped (Goose.Lower.emitTerm term le before).2 := by
  cases live : before.cur with
  | none => rw [emitTerm_none term le live]; exact typed
  | some block =>
    apply typed.modify (types_emitTerm term le before _ _ rfl) block
      (fun body => { body with insts := body.insts.push (.term term) }) (fun _ => rfl)
    exact congrArg (fun pair => pair.2.blocks) (emitTerm_run term le live)

theorem EmittedParametersTyped.patchTerm {before : LS} (typed : EmittedParametersTyped before)
    (le : LEnv) (block : BlockId) (term : Term) :
    EmittedParametersTyped (Goose.Lower.patchTerm block term le before).2 := by
  apply typed.modify (types_patchTerm block term le before _ _ rfl) block
    (fun body => { body with insts := body.insts.push (.term term) }) (fun _ => rfl)
  rfl

end Goose.Lower.Validation
