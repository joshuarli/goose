import Goose.Proofs.ConstructionAcceptedParameterFrameList
import Goose.Proofs.ConstructionRootCorrespondenceScopes

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

inductive ScalarParameterValues (implementation : Impl) : Nat → List Param → List Value → Prop
  | nil (index : Nat) : ScalarParameterValues implementation index [] []
  | cons {index : Nat} {parameter : Param} {value : Value} {parameters : List Param} {values : List Value}
      (parameterAt : implementation.params[index]? = some parameter)
      (descriptor : LocalVar) (declared : implementation.vars[index]? = some descriptor)
      (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
      (represented : ValueRepresentation descriptor.ty value)
      (tail : ScalarParameterValues implementation (index + 1) parameters values) :
      ScalarParameterValues implementation index (parameter :: parameters) (value :: values)

theorem scalarValue_pointerTyped (types : RootTypes) (ty : Ty) (value : Value)
    (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool) (represented : ValueRepresentation ty value) :
    PointerTypedValue types ty value := by
  rcases scalar with ⟨intTy, same⟩ | same
  · rw [same] at represented ⊢
    cases represented with
    | integer intTy number => exact .integer intTy number
    | stored ty value nonfixed => simp [Ty.nonfixed] at nonfixed
  · rw [same] at represented ⊢
    cases represented with
    | boolean boolean => exact .boolean boolean
    | stored ty value nonfixed => simp [Ty.nonfixed] at nonfixed

theorem validatedScalarParameterPlan (config : EvalConfig) (accepted : AcceptedModule config)
    (implementationId : Nat) (implementation : Impl)
    (implementationAt : config.module.impls[implementationId]? = some implementation)
    (scopeInst : Nat) (index : Nat) (parameters : List Param) (values : List Value)
    (checked : ScalarParameterValues implementation index parameters values) :
    ∀ (frame : ConstructionSourceFrame) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
      (outerScopes : List (Nat × Nat)),
      frame.rootCursor.nextVar = index → frame.typingCounter = index →
      frame.typing.variables = implementation.vars → frame.interpretation.environment.vars = implementation.vars →
      frame.interpretation.environment.scopes = (implementation.body.scope, scopeInst) :: outerScopes →
      ∃ finalFrame finalTypes finalLive,
        FreshScalarParameterPlan scopeInst frame types live ((parameters.zip values).map fun (parameter, value) => (parameter.var, value))
          finalFrame finalTypes finalLive := by
  induction checked with
  | nil index =>
    intro frame types live outerScopes rootOrder typingOrder variables runtimeVariables scopes
    exact ⟨frame, types, live, .nil frame types live⟩
  | @cons index parameter value parameters values parameterAt descriptor declared scalar represented tail ih =>
    intro frame types live outerScopes rootOrder typingOrder variables runtimeVariables scopes
    have parameterId := validated_parameter_variable config.module implementationId implementation index parameter accepted.accepted implementationAt parameterAt
    have parameterScope := validated_parameter_scope config.module implementationId implementation index parameter descriptor accepted.accepted implementationAt parameterAt declared
    have bodyScope := validated_body_scope config.module implementationId implementation accepted.accepted implementationAt
    have sameScope : descriptor.scope = implementation.body.scope := parameterScope.trans bodyScope.symm
    have localDeclared : frame.typing.variables[index]? = some descriptor := by simpa [variables] using declared
    have runtimeDeclared : frame.interpretation.environment.vars[index]? = some descriptor := by simpa [runtimeVariables] using declared
    have resolved : ∀ state, rootOf frame.interpretation.environment index state =
        .ok (.local frame.interpretation.environment.act scopeInst index) state := by
      intro state
      simp [rootOf, runtimeDeclared, scopes, sameScope, pure]
    let next := advanceLocalFrame frame index
    let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst index
    obtain ⟨finalFrame, finalTypes, finalLive, tailPlan⟩ := ih next
      (registerRootType types root descriptor.ty) (fun other => other = root ∨ live other) outerScopes
      (by simp [next, advanceLocalFrame, rootOrder]) (by simp [next, advanceLocalFrame, typingOrder])
      (by simpa [next, advanceLocalFrame] using variables) (by simpa [next, advanceLocalFrame] using runtimeVariables)
      (by simpa [next, advanceLocalFrame] using scopes)
    refine ⟨finalFrame, finalTypes, finalLive, ?_⟩
    simp only [List.zip_cons_cons, List.map_cons, parameterId]
    exact .cons rootOrder.symm typingOrder.symm localDeclared resolved scalar represented
      (scalarValue_pointerTyped types descriptor.ty value scalar represented) tailPlan

theorem ScalarParameterValues.lengths {implementation : Impl} {index : Nat} {parameters : List Param} {values : List Value}
    (checked : ScalarParameterValues implementation index parameters values) : parameters.length = values.length := by
  induction checked with
  | nil => rfl
  | cons parameterAt descriptor declared scalar represented tail ih => simpa using ih

theorem bindAll_validatedScalarParameters (config : EvalConfig) (accepted : AcceptedModule config)
    (implementationId : Nat) (implementation : Impl)
    (implementationAt : config.module.impls[implementationId]? = some implementation)
    (scopeInst : Nat) (index : Nat) (parameters : List Param) (values : List Value)
    (checked : ScalarParameterValues implementation index parameters values)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (outerScopes : List (Nat × Nat))
    (rootOrder : frame.rootCursor.nextVar = index) (typingOrder : frame.typingCounter = index)
    (variables : frame.typing.variables = implementation.vars) (runtimeVariables : frame.interpretation.environment.vars = implementation.vars)
    (scopes : frame.interpretation.environment.scopes = (implementation.body.scope, scopeInst) :: outerScopes)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) :
    ∃ after finalTypes finalLive,
      bindAll frame.interpretation.environment.act scopeInst
        ((parameters.zip values).map fun (parameter, value) => (parameter.var, value)) state = .ok () after ∧
      RootTypesExtend types finalTypes ∧ AcceptedWorld config frame.initialized after ambient finalTypes finalLive regions pending ∧
      AcceptedFrame config accepted (advanceParameterFrames frame index parameters.length) after finalTypes := by
  obtain ⟨finalFrame, finalTypes, finalLive, plan⟩ := validatedScalarParameterPlan config accepted implementationId implementation implementationAt
    scopeInst index parameters values checked frame types live outerScopes rootOrder typingOrder variables runtimeVariables scopes
  obtain ⟨after, bound, extended, finalWorld, finalSource⟩ := bindAll_freshScalarList_accepted plan state ambient regions pending world source
  have finalFrameEq := plan.finalFrame
  have lengths := checked.lengths
  simp only [List.length_map, List.length_zip, rootOrder] at finalFrameEq
  rw [← lengths, Nat.min_self] at finalFrameEq
  rw [finalFrameEq] at finalSource
  exact ⟨after, finalTypes, finalLive, bound, extended, finalWorld, finalSource⟩

#print axioms ScalarParameterValues.lengths
#print axioms bindAll_validatedScalarParameters
#print axioms scalarValue_pointerTyped
#print axioms validatedScalarParameterPlan
end Goose.Proofs.ConstructionAcceptedExecution
