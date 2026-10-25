import Goose.GIR.ReplacementContentFlowProofsSliceTouches

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem State.CanonicalWithin.holder_content_normalized {func : Func} {types : Array (Option VTy)}
    {provenance : Prov} {state : State} {payload : Ty} {upper : List RootRef} {address : Roots}
    (before : state.CanonicalWithin func types provenance)
    (physical : HolderRoots func payload upper address)
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    (reference : payload.isRefLike = true)
    (observed : ∀ index mutability, func.params[index]? = some (.ref mutability payload) →
      RootRef.param index ∈ upper → (func.roots.contents.find? (·.1 == index)).isSome = true)
    (ready : content func state address ≠ .pending) :
    ∃ roots, normalize func (content func state address) = some roots := by
  apply Roots.AtomsWithin.normalize (ready := ready)
  cases address with
  | pending => trivial
  | unknown => exact False.elim physical
  | known atoms =>
      apply Roots.AtomsWithin.bind_known
      intro atom member
      cases physical atom member with
      | slot slot storage row type target =>
          have bounded : slot < state.slots.size := by
            rw [before.shape.slots]
            exact (Array.getElem?_eq_some_iff.mp row).choose
          exact (before.memory.slots slot bounded).normalizableAtoms
      | parameter index mutability row target =>
          have slice := paramOk_refLike_payload parameters row reference
          have found : (func.params[index]?).any Ty.isRefSlice = true := by simp [row,slice]
          have bounded : index < state.contents.size := by
            rw [before.shape.contents]
            exact (List.getElem?_eq_some_iff.mp row).choose
          simpa only [found,ite_true] using
            (before.memory.contents index bounded (observed index mutability row target)).normalizableAtoms

#print axioms State.CanonicalWithin.holder_content_normalized

end Goose.GIR.ReplacementContentFlow.Model
