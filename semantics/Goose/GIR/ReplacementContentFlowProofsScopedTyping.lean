import Goose.GIR.ReplacementContentFlowProofsSliceTyping

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

inductive SliceViewType : VTy → Prop
  | slice (mutability : Mutability) (element : Ty) : SliceViewType (.data (.slice mutability element))
  | view (mutability : Mutability) (element : Ty) : SliceViewType (.view mutability element)

theorem SliceViewType.reference {type : VTy} (carrier : SliceViewType type) : type.refLike = true := by
  cases carrier <;> rfl

theorem refLike_type_cases {type : VTy} (reference : type.refLike = true) :
    SliceViewType type ∨ ∃ mutability payload, type = .data (.ref mutability payload) := by
  cases type with
  | view mutability element => exact Or.inl (.view mutability element)
  | data type =>
      cases type <;> simp [VTy.refLike,Ty.isRefLike] at reference
      case ref mutability payload => exact Or.inr ⟨mutability,payload,rfl⟩
      case slice mutability element => exact Or.inl (.slice mutability element)

theorem valRefLike_type_cases {types : Array (Option VTy)} {value : ValueId}
    (reference : valRefLike types value = true) :
    ∃ type, types[value]? = some (some type) ∧
      (SliceViewType type ∨ ∃ mutability payload, type = .data (.ref mutability payload)) := by
  unfold valRefLike at reference
  cases row : types[value]? with
  | none => simp [row] at reference
  | some actual =>
      cases actual with
      | none => simp [row] at reference
      | some type =>
          simp only [row] at reference
          exact ⟨type,rfl,refLike_type_cases reference⟩

private theorem scoped_bind_ok {α β : Type} (result : Except String α) (next : α → Except String β) (value : β) :
    (result >>= next) = .ok value ↔ ∃ prior, result = .ok prior ∧ next prior = .ok value := by
  cases result <;> simp [bind,Except.bind]

theorem SliceDefinition.of_view_resultTy {env : TyEnv}
    (values : ValueTypeShapes env.vals)
    (globals : ∀ (index : Nat) (type : Ty) (kind : VarKind), env.globals[index]? = some (type,kind) → type.isRefLike = false)
    (fields : ∀ (index : Nat) (descriptor : StructDef), env.structs[index]? = some descriptor →
      ∀ (fieldIndex : Nat) (field : StructField), descriptor.fields[fieldIndex]? = some field → field.ty.flat = true)
    (op : Op) {mutability : Mutability} {element : Ty}
    (typed : op.resultTy env = .ok (.view mutability element)) : SliceDefinition env op := by
  have classified := DefinitionTyping.of_resultTy values globals fields op typed
  cases classified with
  | scalar op type ordinary scalar => simp [VTy.refLike] at scalar
  | call fn args origin type => exact .call fn args origin
  | backing op source type backing target =>
      cases backing with
      | snapshot mode source =>
          simp only [Op.resultTy] at typed
          obtain ⟨⟨mu,owner⟩,reference,_⟩ := (scoped_bind_ok _ _ _).mp typed
          refine .backing _ source (.snapshot mode source) (by intro; simp [accessOperands,Inst.uses,Op.uses]) ?_
          simp [valRefLike,TyEnv.refTy_known reference,VTy.refLike,Ty.isRefLike]
      | view source =>
          simp only [Op.resultTy] at typed
          obtain ⟨sourceTy,known,typed⟩ := (scoped_bind_ok _ _ _).mp typed
          cases sourceTy <;> simp only [tyErr] at typed
          all_goals try cases typed
          exact .backing _ source (.view source) (by intro; simp [accessOperands,Inst.uses,Op.uses])
            (by simp [valRefLike,TyEnv.dataTy_known known,VTy.refLike,Ty.isRefLike])
      | slice mu source low high origin =>
          simp only [Op.resultTy] at typed
          obtain ⟨⟨oldMu,elem⟩,_,typed⟩ := (scoped_bind_ok _ _ _).mp typed
          repeat' first
            | (obtain ⟨_,_,typed⟩ := (scoped_bind_ok _ _ _).mp typed)
            | (split at typed)
          all_goals simp_all [tyErr,bind,Except.bind,pure,Except.pure]
      | element source index | checked source index origin | proven source index =>
          simp only [Op.resultTy] at typed
          obtain ⟨⟨mu,elem⟩,_,typed⟩ := (scoped_bind_ok _ _ _).mp typed
          obtain ⟨_,_,typed⟩ := (scoped_bind_ok _ _ _).mp typed
          cases typed
      | push source value origin =>
          simp only [Op.resultTy] at typed
          obtain ⟨⟨mu,owner⟩,_,typed⟩ := (scoped_bind_ok _ _ _).mp typed
          cases selected : owner.ownerElem? with
          | none => simp [selected,tyErr] at typed
          | some elem =>
              simp only [selected] at typed
              repeat' first
                | (obtain ⟨_,_,typed⟩ := (scoped_bind_ok _ _ _).mp typed)
                | (split at typed)
              all_goals simp_all [tyErr,bind,Except.bind,pure,Except.pure]
      | field source fieldIndex =>
          simp only [Op.resultTy] at typed
          obtain ⟨⟨mu,owner⟩,_,typed⟩ := (scoped_bind_ok _ _ _).mp typed
          cases owner with
          | structT id fieldTypes =>
              cases descriptorAt : env.structs[id]? with
              | none => simp [descriptorAt,tyErr] at typed
              | some descriptor =>
                  simp only [descriptorAt] at typed
                  split at typed
                  · cases fieldAt : descriptor.fields[fieldIndex]? with
                    | none => simp [fieldAt,tyErr] at typed
                    | some field => simp [fieldAt,pure,Except.pure] at typed
                  · simp [tyErr,bind,Except.bind] at typed
          | _ => cases typed

theorem SliceDefinition.of_carrier_resultTy {env : TyEnv}
    (values : ValueTypeShapes env.vals)
    (globals : ∀ (index : Nat) (type : Ty) (kind : VarKind), env.globals[index]? = some (type,kind) → type.isRefLike = false)
    (fields : ∀ (index : Nat) (descriptor : StructDef), env.structs[index]? = some descriptor →
      ∀ (fieldIndex : Nat) (field : StructField), descriptor.fields[fieldIndex]? = some field → field.ty.flat = true)
    (op : Op) {type : VTy} (carrier : SliceViewType type)
    (typed : op.resultTy env = .ok type) : SliceDefinition env op := by
  cases carrier with
  | slice => exact SliceDefinition.of_resultTy values globals fields op typed
  | view => exact SliceDefinition.of_view_resultTy values globals fields op typed

end Goose.GIR.ReplacementContentFlow.Model
