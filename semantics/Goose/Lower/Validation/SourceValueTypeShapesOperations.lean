import Goose.Lower.Validation.SourceValueTypeShapes

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

def ShapeAnnotation : Inst → Prop
  | .def _ (.structLit type _) | .def _ (.arrLit type _) | .def _ (.arrFill type _) =>
      type.storable = true
  | _ => True

structure ShapeTyEnv (env : TyEnv) : Prop where
  values : ValueTypeShapes env.vals
  slots : ∀ (index : Nat) (descriptor : Slot), env.slots[index]? = some descriptor → descriptor.ty.paramOk = true
  globals : ∀ (index : Nat) (type : Ty) (kind : VarKind), env.globals[index]? = some (type, kind) → type.storable = true
  signatures : ∀ (index : Nat) (params results : List Ty), env.sigs[index]? = some (params, results) →
    ∀ type ∈ results, type.storable = true
  fields : ∀ (index : Nat) (descriptor : StructDef), env.structs[index]? = some descriptor →
    ∀ (fieldIndex : Nat) (field : StructField), descriptor.fields[fieldIndex]? = some field → field.ty.flat = true

theorem op_resultTy_shape {env : TyEnv}
    (resolved : ShapeTyEnv env) (op : Op) {type : VTy}
    (annotation : ∀ value, ShapeAnnotation (.def value op))
    (typed : op.resultTy env = .ok type) : ValueTypeShape type := by
  cases op with
  | constInt integer number =>
    simp only [Op.resultTy] at typed
    split at typed
    · cases typed
      simp [ValueTypeShape, DataTypeShape, Ty.storable]
    · cases typed
  | constBool value => cases typed; simp [ValueTypeShape, DataTypeShape, Ty.storable]
  | constUnit => cases typed; simp [ValueTypeShape, DataTypeShape, Ty.storable]
  | bin operator integer left right origin
  | cmp operator integer left right
  | boolCmp operator left right
  | boolNot value
  | next integer value
  | viewLen value =>
    simp only [Op.resultTy] at typed
    try simp only [Core.Sound.ex_bind_ok] at typed
    repeat' first
      | (rcases typed with ⟨_, _, typed⟩)
      | (split at typed <;> try simp only [Core.Sound.ex_bind_ok] at typed)
    all_goals try simp_all only [tyErr, bind, Except.bind, pure, Except.pure, reduceCtorEq]
    all_goals simp [ValueTypeShape, DataTypeShape, Ty.storable]
  | un operator integer value origin | conv conversion source destination value origin =>
    simp only [Op.resultTy] at typed
    try simp only [Core.Sound.ex_bind_ok] at typed
    repeat' first
      | (rcases typed with ⟨_, _, typed⟩)
      | (split at typed <;> try simp only [Core.Sound.ex_bind_ok] at typed)
    all_goals try simp_all only [tyErr, bind, Except.bind, pure, Except.pure, reduceCtorEq]
    all_goals simp [ValueTypeShape, DataTypeShape, Ty.storable]
  | slotAddr slot =>
    simp only [Op.resultTy] at typed
    cases row : env.slots[slot]? with
    | none => simp [row, tyErr] at typed
    | some descriptor =>
      simp only [row] at typed
      cases typed
      exact dataTypeShape_reference (by
        simpa only [Ty.paramOk, Bool.or_eq_true] using resolved.slots slot descriptor row)
  | globalAddr global =>
    simp only [Op.resultTy] at typed
    cases row : env.globals[global]? with
    | none => simp [row, tyErr] at typed
    | some descriptor =>
      obtain ⟨source, kind⟩ := descriptor
      simp only [row] at typed
      cases typed
      exact dataTypeShape_reference (Or.inl (resolved.globals global source kind row))
  | refElem value index | indexChecked value index origin | indexProven value index =>
    simp only [Op.resultTy] at typed
    obtain ⟨⟨mu, element⟩, view, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    obtain ⟨_, _, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    cases typed
    all_goals exact dataTypeShape_reference (Or.inl (shape_flat_storable (resolved.values.view view)))
  | refFreeze value =>
    simp only [Op.resultTy] at typed
    obtain ⟨⟨mu, element⟩, reference, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    cases typed
    exact dataTypeShape_reference (resolved.values.reference reference)
  | load value =>
    simp only [Op.resultTy] at typed
    obtain ⟨⟨mu, element⟩, reference, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    cases typed
    exact dataTypeShape_load (resolved.values.reference reference)
  | ownerBorrow value =>
    simp only [Op.resultTy] at typed
    obtain ⟨⟨mu, source⟩, reference, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    dsimp only at typed
    split at typed
    · cases source <;> simp only [tyErr] at typed
      all_goals cases typed
      all_goals exact dataTypeShape_reference (resolved.values.reference reference)
    · simp [tyErr, bind, Except.bind] at typed
  | snapshot mode value =>
    simp only [Op.resultTy] at typed
    obtain ⟨⟨mu, source⟩, reference, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    cases selected : GIR.arrayElem? source with
    | none => simp [selected, tyErr] at typed
    | some element =>
      simp only [selected] at typed
      cases typed
      exact dataTypeShape_array_element (resolved.values.reference reference) selected
  | sliceView value =>
    simp only [Op.resultTy] at typed
    obtain ⟨source, data, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    cases source <;> try (cases typed)
    exact dataTypeShape_slice_element (resolved.values value _ (TyEnv.dataTy_known data))
  | viewSlice mu value low high origin =>
    simp only [Op.resultTy] at typed
    obtain ⟨⟨oldMu, element⟩, view, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    try simp only [Core.Sound.ex_bind_ok] at typed
    repeat' first
      | (rcases typed with ⟨_, _, typed⟩)
      | (split at typed <;> try simp only [Core.Sound.ex_bind_ok] at typed)
    all_goals try simp_all only [tyErr, bind, Except.bind, pure, Except.pure, reduceCtorEq]
    all_goals exact Or.inr (Or.inl (resolved.values.view view))
  | arrayLen value =>
    simp only [Op.resultTy] at typed
    obtain ⟨⟨mu, source⟩, _, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    split at typed <;> cases typed
    simp [ValueTypeShape, DataTypeShape, Ty.storable]
  | push owner value origin =>
    simp only [Op.resultTy] at typed
    obtain ⟨⟨mu, source⟩, reference, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    cases selected : source.ownerElem? with
    | none => simp [selected, tyErr] at typed
    | some element =>
      simp only [selected] at typed
      try simp only [Core.Sound.ex_bind_ok] at typed
      repeat' first
        | (rcases typed with ⟨_, _, typed⟩)
        | (split at typed <;> try simp only [Core.Sound.ex_bind_ok] at typed)
      all_goals try simp_all only [tyErr, bind, Except.bind, pure, Except.pure, reduceCtorEq]
      all_goals exact dataTypeShape_reference (Or.inl
        (shape_flat_storable (dataTypeShape_owner_element (resolved.values.reference reference) selected)))
  | pop owner origin =>
    simp only [Op.resultTy] at typed
    obtain ⟨⟨mu, source⟩, reference, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    cases selected : source.ownerElem? with
    | none => simp [selected, tyErr] at typed
    | some element =>
      simp only [selected] at typed
      cases typed
      all_goals exact dataTypeShape_of_flat (dataTypeShape_owner_element (resolved.values.reference reference) selected)
  | call function args origin =>
    simp only [Op.resultTy] at typed
    cases signature : env.sigs[function]? with
    | none => simp [signature, tyErr] at typed
    | some pair =>
      obtain ⟨params, results⟩ := pair
      simp only [signature] at typed
      try simp only [Core.Sound.ex_bind_ok] at typed
      repeat' first
        | (rcases typed with ⟨_, _, typed⟩)
        | (split at typed <;> try simp only [Core.Sound.ex_bind_ok] at typed)
      all_goals try simp_all only [tyErr, bind, Except.bind, pure, Except.pure, reduceCtorEq]
      all_goals first
        | (solve | simp [ValueTypeShape, DataTypeShape, Ty.storable])
        | exact Or.inr (Or.inl (resolved.signatures function _ _ signature _ (by simp)))
  | arrLit source values =>
    have valid := annotation 0
    change source.storable = true at valid
    simp only [Op.resultTy] at typed
    cases source <;> try (cases typed)
    all_goals try simp only [Core.Sound.ex_bind_ok] at typed
    repeat' first
      | (rcases typed with ⟨_, _, typed⟩)
      | (split at typed <;> try simp only [Core.Sound.ex_bind_ok] at typed)
    all_goals try simp_all only [tyErr, bind, Except.bind, pure, Except.pure, reduceCtorEq]
    all_goals exact Or.inr (Or.inl valid)
  | arrFill source value =>
    have valid := annotation 0
    change source.storable = true at valid
    simp only [Op.resultTy] at typed
    cases source <;> try (cases typed)
    try simp only [Core.Sound.ex_bind_ok] at typed
    repeat' first
      | (rcases typed with ⟨_, _, typed⟩)
      | (split at typed <;> try simp only [Core.Sound.ex_bind_ok] at typed)
    all_goals try simp_all only [tyErr, bind, Except.bind, pure, Except.pure, reduceCtorEq]
    all_goals exact Or.inr (Or.inl valid)
  | structLit source values =>
    have valid := annotation 0
    change source.storable = true at valid
    simp only [Op.resultTy] at typed
    try simp only [Core.Sound.ex_bind_ok] at typed
    repeat' first
      | (rcases typed with ⟨_, _, typed⟩)
      | (split at typed <;> try simp only [Core.Sound.ex_bind_ok] at typed)
    all_goals try simp_all only [tyErr, bind, Except.bind, pure, Except.pure, reduceCtorEq]
    all_goals exact Or.inr (Or.inl valid)
  | fieldAddr owner fieldIndex =>
    simp only [Op.resultTy] at typed
    obtain ⟨⟨mu, source⟩, _, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    cases source with
    | structT id fields =>
      cases descriptorAt : env.structs[id]? with
      | none => simp [descriptorAt, tyErr] at typed
      | some descriptor =>
        dsimp only at typed
        simp only [descriptorAt] at typed
        split at typed
        · cases fieldAt : descriptor.fields[fieldIndex]? with
          | none => simp [fieldAt, tyErr] at typed
          | some field =>
            simp only [fieldAt] at typed
            cases typed
            exact dataTypeShape_reference (Or.inl (shape_flat_storable
              (resolved.fields id descriptor descriptorAt fieldIndex field fieldAt)))
        · simp [tyErr, bind, Except.bind] at typed
    | _ => cases typed


#print axioms op_resultTy_shape

end Goose.Lower.Validation
