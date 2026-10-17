import Goose.Lower.Validation.PermissionPreservationSourceTransfers
import Goose.Lower.Validation.PermissionPreservationTargets

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem referenceWritable_binding_or_owner {profile : ArtifactProfile} {info : PlaceInfo}
    (writable : info.referenceWritable profile = true) (demand : BindingTarget profile info.ty) :
    info.bindingWritable = true ∨
      (profile = .shrink ∧ info.contentsWritable = true ∧
        ((∃ element, info.ty = .grow element) ∨ (∃ element, info.ty = .growshrink element))) := by
  cases shape : info.ty with
  | grow element =>
    have shrink : profile = .shrink := by simpa only [BindingTarget, shape] using demand
    exact Or.inr ⟨shrink, by simpa only [PlaceInfo.referenceWritable, shape] using writable,
      Or.inl ⟨element, rfl⟩⟩
  | growshrink element =>
    have shrink : profile = .shrink := by simpa only [BindingTarget, shape] using demand
    exact Or.inr ⟨shrink, by simpa only [PlaceInfo.referenceWritable, shape, shrink, beq_self_eq_true, ite_true] using writable,
      Or.inr ⟨element, rfl⟩⟩
  | _ => exact Or.inl (by simpa only [PlaceInfo.referenceWritable, shape] using writable)

theorem source_mutable_reference_binding {env : Core.TEnv} {place : Place} {referent : Ty}
    {start finish : Nat}
    (source : Core.tyExpr env (.ref .mutable place) start = .ok (.ref .mutable referent, finish))
    (demand : BindingTarget env.mod.profile referent) :
    ∃ info next, Core.tyPlace env place start = .ok (info, next) ∧ info.ty = referent ∧
      info.canReference place = true ∧
      (info.bindingWritable = true ∨
        (env.mod.profile = .shrink ∧ info.contentsWritable = true ∧
          ((∃ element, info.ty = .grow element) ∨ (∃ element, info.ty = .growshrink element)))) := by
  obtain ⟨info, next, placeSource, shape, reference, writable⟩ := source_mutable_reference_permissions source
  have same := (Ty.ref.inj shape).2
  refine ⟨info, next, placeSource, same.symm, reference, ?_⟩
  exact referenceWritable_binding_or_owner writable (by simpa only [same] using demand)

#print axioms referenceWritable_binding_or_owner
#print axioms source_mutable_reference_binding

end Goose.Lower.Validation
