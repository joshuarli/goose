import Goose.Proofs.ConstructionAcceptedValidatedParameterList

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

inductive ScalarParameterDescriptors (implementation : Impl) : Nat → List Param → List Ty → Prop
  | nil (index : Nat) : ScalarParameterDescriptors implementation index [] []
  | cons {index : Nat} {parameter : Param} {parameters : List Param} {types : List Ty}
      (parameterAt : implementation.params[index]? = some parameter)
      (descriptor : LocalVar) (declared : implementation.vars[index]? = some descriptor)
      (mode : parameter.mode = .byValue)
      (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
      (tail : ScalarParameterDescriptors implementation (index + 1) parameters types) :
      ScalarParameterDescriptors implementation index (parameter :: parameters) (descriptor.ty :: types)

theorem validatedScalarParameterDescriptors (config : EvalConfig) (accepted : AcceptedModule config)
    (implementationId : Nat) (implementation : Impl)
    (implementationAt : config.module.impls[implementationId]? = some implementation)
    (index : Nat) (parameters : List Param)
    (indexed : ∀ offset parameter, parameters[offset]? = some parameter →
      implementation.params[index + offset]? = some parameter)
    (modes : ∀ parameter ∈ parameters, parameter.mode = .byValue)
    (scalars : ∀ parameter ∈ parameters, ∀ descriptor, implementation.vars[parameter.var]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    ∃ types, ScalarParameterDescriptors implementation index parameters types := by
  induction parameters generalizing index with
  | nil => exact ⟨[], .nil index⟩
  | cons parameter rest ih =>
    have parameterAt : implementation.params[index]? = some parameter := by
      have found := indexed 0 parameter (by simp)
      simpa using found
    have parameterId := validated_parameter_variable config.module implementationId implementation index parameter accepted.accepted implementationAt parameterAt
    obtain ⟨descriptor, descriptorAt⟩ := validated_parameter_descriptor config.module implementationId implementation index parameter accepted.accepted implementationAt parameterAt
    have declared : implementation.vars[index]? = some descriptor := by simpa [parameterId] using descriptorAt
    have mode := modes parameter (by simp)
    have scalar := scalars parameter (by simp) descriptor descriptorAt
    have tailIndexed : ∀ offset item, rest[offset]? = some item → implementation.params[index + 1 + offset]? = some item := by
      intro offset item found
      have whole : (parameter :: rest)[offset + 1]? = some item := by simpa using found
      have selected := indexed (offset + 1) item whole
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using selected
    obtain ⟨types, tail⟩ := ih (index + 1) tailIndexed
      (by intro item member; exact modes item (by simp [member]))
      (by intro item member; exact scalars item (by simp [member]))
    exact ⟨descriptor.ty :: types, .cons parameterAt descriptor declared mode scalar tail⟩

theorem validatedScalarParameterDescriptors_all (config : EvalConfig) (accepted : AcceptedModule config)
    (implementationId : Nat) (implementation : Impl)
    (implementationAt : config.module.impls[implementationId]? = some implementation)
    (modes : ∀ parameter ∈ implementation.params.toList, parameter.mode = .byValue)
    (scalars : ∀ parameter ∈ implementation.params.toList, ∀ descriptor, implementation.vars[parameter.var]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    ∃ types, ScalarParameterDescriptors implementation 0 implementation.params.toList types := by
  apply validatedScalarParameterDescriptors config accepted implementationId implementation implementationAt 0 implementation.params.toList
  · intro offset parameter found
    simpa using found
  · exact modes
  · exact scalars

#print axioms validatedScalarParameterDescriptors
#print axioms validatedScalarParameterDescriptors_all
end Goose.Proofs.ConstructionAcceptedExecution
