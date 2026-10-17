import Goose.GIR.ReplacementContentFlowProofsCanonicalTypes
import Goose.Lower.Validation.SourceReadableTypes

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem shape_flat_storable {type : Ty} (flat : type.flat = true) : type.storable = true := by
  cases type <;> simp_all [Ty.flat, Ty.storable]

theorem dataTypeShape_of_flat {type : Ty} (flat : type.flat = true) : DataTypeShape type := by
  apply Or.inr ∘ Or.inl
  cases type <;> simp_all [Ty.flat, Ty.storable]

theorem dataTypeShape_of_paramOk {type : Ty} (allowed : type.paramOk = true) :
    DataTypeShape type := by
  simp only [Ty.paramOk, Bool.or_eq_true] at allowed
  rcases allowed with stored | reference
  · exact Or.inr (Or.inl stored)
  · cases type with
    | ref mutability payload =>
      cases payload with
      | slice sliceMutability element =>
        exact Or.inr (Or.inr ⟨mutability, .slice sliceMutability element, rfl, Or.inl reference⟩)
      | _ => simp [Ty.isRefSlice] at reference
    | _ => simp [Ty.isRefSlice] at reference

theorem dataTypeShape_of_readable {type : Ty} (readable : type.readable = true) :
    DataTypeShape type := Or.inr (Or.inl (source_readable_storable readable))

theorem dataTypeShape_reference {mutability : Mutability} {payload : Ty}
    (allowed : payload.storable = true ∨ payload.isRefSlice = true) :
    DataTypeShape (.ref mutability payload) :=
  Or.inr (Or.inr ⟨mutability, payload, rfl, allowed⟩)

theorem dataTypeShape_load {payload : Ty}
    (allowed : payload.storable = true ∨ payload.isRefSlice = true) : DataTypeShape payload := by
  rcases allowed with stored | reference
  · exact Or.inr (Or.inl stored)
  · exact dataTypeShape_of_paramOk (by simp [Ty.paramOk, reference])

theorem dataTypeShape_slice_element {mutability : Mutability} {element : Ty}
    (shape : DataTypeShape (.slice mutability element)) : element.flat = true := by
  rcases shape with impossible | stored | ⟨_, _, impossible, _⟩
  · cases impossible
  · exact stored
  · cases impossible

theorem dataTypeShape_owner_element {type element : Ty}
    (allowed : type.storable = true ∨ type.isRefSlice = true)
    (owner : type.ownerElem? = some element) : element.flat = true := by
  rcases allowed with stored | reference
  · exact storable_owner_element stored owner
  · cases type <;> simp_all [Ty.isRefSlice, Ty.ownerElem?]

theorem dataTypeShape_array_element {type element : Ty}
    (allowed : type.storable = true ∨ type.isRefSlice = true)
    (array : arrayElem? type = some element) : element.flat = true := by
  rcases allowed with stored | reference
  · cases type <;> simp_all [Ty.storable, arrayElem?]
  · cases type <;> simp_all [Ty.isRefSlice, arrayElem?]

#print axioms dataTypeShape_of_paramOk
#print axioms dataTypeShape_array_element

end Goose.Lower.Validation
