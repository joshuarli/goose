import Goose.Lower.Validation.PermissionPreservationTransport
import Goose.Lower.Validation.ExpressionTypingSourceContents
import Goose.Lower.Validation.PermissionPreservationTargets

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem passableTo_mutable_reference {source referent : Ty}
    (compatible : source.passableTo (.ref .mutable referent) = true) :
    source = .ref .mutable referent := by
  cases source with
  | ref mu target =>
    cases mu with
    | readOnly => simp [Ty.passableTo, Mutability.atLeast] at compatible
    | mutable =>
      have same : target = referent := eq_of_beq (Bool.and_eq_true_iff.mp compatible).1
      subst target
      rfl
  | _ => simp [Ty.passableTo] at compatible

theorem PermissionTransfer.of_source {profile : ArtifactProfile} {writable contents : ValueId → Prop} {value : ValueId}
    {source target : Ty} (compatible : source.passableTo target = true)
    (bindings : ∀ referent, source = .ref .mutable referent → BindingTarget profile referent → writable value)
    (elements : ∀ referent, source = .ref .mutable referent → ContentsTarget referent → contents value) :
    PermissionTransfer profile writable contents value target := by
  cases target with
  | ref mu referent =>
    cases mu with
    | readOnly => trivial
    | mutable =>
      have same := passableTo_mutable_reference compatible
      cases profile <;> cases referent <;> simp only [PermissionTransfer, reduceCtorEq, ↓reduceIte] <;>
        first | exact elements _ same trivial
              | exact ⟨bindings _ same (by simp [BindingTarget]), elements _ same trivial⟩
              | exact bindings _ same (by simp [BindingTarget])
  | _ => trivial

#print axioms passableTo_mutable_reference
#print axioms PermissionTransfer.of_source

end Goose.Lower.Validation
