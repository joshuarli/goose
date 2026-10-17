import Goose.GIR.ReplacementContentFlow

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

def DataTypeShape (type : Ty) : Prop :=
  type = .unit ∨ type.storable = true ∨
    ∃ mutability payload, type = .ref mutability payload ∧
      (payload.storable = true ∨ payload.isRefSlice = true)

def ValueTypeShape : VTy → Prop
  | .data type => DataTypeShape type
  | .view _ element => element.flat = true

def ValueTypeShapes (types : Array (Option VTy)) : Prop :=
  ∀ (value : ValueId) (type : VTy), types[value]? = some (some type) → ValueTypeShape type

theorem refTarget_storable {type : Ty} (target : type.refTarget = true) : type.storable = true := by
  cases type <;> simp_all [Ty.refTarget,Ty.storable]

theorem DataTypeShape.reference {mutability : Mutability} {payload : Ty}
    (shape : DataTypeShape (.ref mutability payload)) :
    payload.storable = true ∨ payload.isRefSlice = true := by
  rcases shape with impossible | storable | ⟨actualMutability,actualPayload,same,actualShape⟩
  · cases impossible
  · exact Or.inl (refTarget_storable storable)
  · have same : actualPayload = payload := (Ty.ref.inj same).2.symm
    simpa only [same] using actualShape

theorem flat_not_address {type : Ty} (flat : type.flat = true) :
    type.isRefLike = false ∧ type.ownerElem?.isSome = false := by
  cases type <;> simp_all [Ty.flat,Ty.isRefLike,Ty.ownerElem?]

theorem storable_owner_element {type element : Ty} (storable : type.storable = true)
    (owner : type.ownerElem? = some element) : element.flat = true := by
  cases type <;> simp_all [Ty.storable,Ty.ownerElem?]

theorem storable_struct_fields {id : StructId} {fields : TyList}
    (storable : (Ty.structT id fields).storable = true) : fields.flat = true := storable

theorem readable_not_holder {mutability : Mutability} {payload : Ty}
    (readable : (Ty.ref mutability payload).readable = true) : payload.isRefLike = false := by
  cases payload <;> simp_all [Ty.readable,Ty.refTarget,Ty.isRefLike]

theorem TyEnv.valTy_known {env : TyEnv} {value : ValueId} {type : VTy}
    (known : env.valTy value = .ok type) : env.vals[value]? = some (some type) := by
  unfold TyEnv.valTy at known
  split at known
  · cases known
    assumption
  · cases known

theorem TyEnv.dataTy_known {env : TyEnv} {value : ValueId} {type : Ty}
    (known : env.dataTy value = .ok type) : env.vals[value]? = some (some (.data type)) := by
  unfold TyEnv.dataTy at known
  cases found : env.valTy value with
  | error error => simp [found,bind,Except.bind] at known
  | ok actual =>
      cases actual with
      | data actual =>
          have same : actual = type := by simpa [found,bind,Except.bind,pure,Except.pure] using known
          subst actual
          exact TyEnv.valTy_known found
      | view _ _ => simp [found,bind,Except.bind,tyErr] at known

theorem TyEnv.refTy_known {env : TyEnv} {value : ValueId} {mutability : Mutability} {payload : Ty}
    (known : env.refTy value = .ok (mutability,payload)) :
    env.vals[value]? = some (some (.data (.ref mutability payload))) := by
  unfold TyEnv.refTy at known
  cases found : env.dataTy value with
  | error error => simp [found,bind,Except.bind] at known
  | ok actual =>
      cases actual <;> simp [found,bind,Except.bind,pure,Except.pure,tyErr] at known
      obtain ⟨rfl,rfl⟩ := known
      exact TyEnv.dataTy_known found

theorem TyEnv.viewTy_known {env : TyEnv} {value : ValueId} {mutability : Mutability} {element : Ty}
    (known : env.viewTy value = .ok (mutability,element)) :
    env.vals[value]? = some (some (.view mutability element)) := by
  unfold TyEnv.viewTy at known
  cases found : env.valTy value with
  | error error => simp [found,bind,Except.bind] at known
  | ok actual =>
      cases actual with
      | data _ => simp [found,bind,Except.bind,tyErr] at known
      | view actualMutability actualElement =>
          obtain ⟨rfl,rfl⟩ : actualMutability = mutability ∧ actualElement = element := by
            simpa [found,bind,Except.bind,pure,Except.pure] using known
          exact TyEnv.valTy_known found

theorem ValueTypeShapes.reference {env : TyEnv} {value : ValueId} {mutability : Mutability} {payload : Ty}
    (closed : ValueTypeShapes env.vals) (known : env.refTy value = .ok (mutability,payload)) :
    payload.storable = true ∨ payload.isRefSlice = true :=
  DataTypeShape.reference (closed value _ (TyEnv.refTy_known known))

theorem ValueTypeShapes.view {env : TyEnv} {value : ValueId} {mutability : Mutability} {element : Ty}
    (closed : ValueTypeShapes env.vals) (known : env.viewTy value = .ok (mutability,element)) :
    element.flat = true := closed value _ (TyEnv.viewTy_known known)

#print axioms DataTypeShape.reference
#print axioms ValueTypeShapes.reference
#print axioms ValueTypeShapes.view

end Goose.GIR.ReplacementContentFlow.Model
