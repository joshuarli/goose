import Goose.Construct.Validate
import Goose.Proofs.ConstructionReadTypingLayout

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private theorem layout_bind_success {α β : Type} (action : Goose.Core.V α)
    (next : α → Goose.Core.V β) (result : β) :
    (action >>= next) = .ok result ↔ ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action <;> simp [bind, Except.bind]

private theorem checkTypes_layoutConforms (module : Module) :
    (∀ ty, checkType module ty = .ok () → LayoutConforms (.ofModule module) ty) ∧
    (∀ fields, checkTypes module fields = .ok () → LayoutFieldsConforms (.ofModule module) fields) := by
  apply checkType.mutual_induct module
    (motive_1 := fun ty => checkType module ty = .ok () → LayoutConforms (.ofModule module) ty)
    (motive_2 := fun fields => checkTypes module fields = .ok () → LayoutFieldsConforms (.ofModule module) fields)
  case case22 =>
    intro ty rest left right checked
    obtain ⟨value, first, remaining⟩ := (layout_bind_success _ _ _).mp checked
    cases value
    exact ⟨left first, right remaining⟩
  all_goals intros
  all_goals simp_all [checkType, checkTypes, LayoutConforms, LayoutFieldsConforms,
    Goose.Core.reject, bind, Except.bind, LayoutEnv.structType?, LayoutEnv.ofModule, Module.structType?]
  all_goals split at * <;> simp_all

theorem checkType_layoutConforms (module : Module) (ty : Ty)
    (checked : checkType module ty = .ok ()) : LayoutConforms (.ofModule module) ty :=
  (checkTypes_layoutConforms module).1 ty checked

private theorem type_or_reference_layoutConforms (module : Module) (ty : Ty)
    (checked : checkType module ty = .ok () ∨
      ∃ mutability target, ty = .ref mutability target ∧ checkType module target = .ok ()) :
    LayoutConforms (.ofModule module) ty := by
  rcases checked with checked | ⟨mutability, target, same, checked⟩
  · exact checkType_layoutConforms module ty checked
  · subst ty
    exact checkType_layoutConforms module target checked

theorem validated_global_layoutConforms (module : Module) (id : Nat) (descriptor : Global)
    (accepted : validate module = .ok ()) (present : module.globals[id]? = some descriptor) :
    LayoutConforms (.ofModule module) descriptor.ty :=
  type_or_reference_layoutConforms module descriptor.ty
    (validated_global_type_or_reference module id descriptor accepted present)

theorem validated_local_layoutConforms (module : Module) (implementationId : Nat)
    (implementation : Impl) (id : Nat) (descriptor : LocalVar)
    (accepted : validate module = .ok ()) (implementationAt : module.impls[implementationId]? = some implementation)
    (present : implementation.vars[id]? = some descriptor) :
    LayoutConforms (.ofModule module) descriptor.ty :=
  type_or_reference_layoutConforms module descriptor.ty
    (validated_local_type_or_reference module implementationId implementation id descriptor accepted implementationAt present)

theorem validated_result_layoutConforms (module : Module) (implementationId : Nat)
    (implementation : Impl) (id : Nat) (descriptor : ResultDescriptor)
    (accepted : validate module = .ok ()) (implementationAt : module.impls[implementationId]? = some implementation)
    (present : implementation.results[id]? = some descriptor) :
    LayoutConforms (.ofModule module) descriptor.ty :=
  type_or_reference_layoutConforms module descriptor.ty
    (validated_result_type_or_reference module implementationId implementation id descriptor accepted implementationAt present)

end Goose.Proofs.ConstructionAcceptedExecution
