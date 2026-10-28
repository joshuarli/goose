import Goose.Proofs.ConstructionAcceptedValidatedParameterList

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem FreshScalarParameterPlan.typesOutside {scope : Nat} {frame : ConstructionSourceFrame}
    {types : RootTypes} {live : Goose.Core.RootInst → Prop} {values : List (Nat × Value)}
    {finalFrame : ConstructionSourceFrame} {finalTypes : RootTypes} {finalLive : Goose.Core.RootInst → Prop}
    (plan : FreshScalarParameterPlan scope frame types live values finalFrame finalTypes finalLive) :
    ∀ root, (∀ id, root ≠ .local frame.interpretation.environment.act scope id) → finalTypes root = types root := by
  induction plan with
  | nil frame types live => intros; rfl
  | @cons frame types live id descriptor value rest finalFrame finalTypes finalLive rootOrder typingOrder declared resolved scalar represented pointers tail ih =>
    intro root outside
    have after := ih root (by simpa [advanceLocalFrame] using outside)
    have different := outside id
    simpa [registerRootType, different] using after

theorem bindAll_validatedScalarParameters_protected (config : EvalConfig) (accepted : AcceptedModule config)
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
      RootTypesExtend types finalTypes ∧
      (∀ root, (∀ id, root ≠ .local frame.interpretation.environment.act scopeInst id) → finalTypes root = types root) ∧
      AcceptedWorld config frame.initialized after ambient finalTypes finalLive regions pending ∧
      AcceptedFrame config accepted (advanceParameterFrames frame index parameters.length) after finalTypes := by
  obtain ⟨finalFrame, finalTypes, finalLive, plan⟩ := validatedScalarParameterPlan config accepted implementationId implementation implementationAt
    scopeInst index parameters values checked frame types live outerScopes rootOrder typingOrder variables runtimeVariables scopes
  obtain ⟨after, bound, extended, finalWorld, finalSource⟩ := bindAll_freshScalarList_accepted plan state ambient regions pending world source
  have finalFrameEq := plan.finalFrame
  have lengths := checked.lengths
  simp only [List.length_map, List.length_zip, rootOrder] at finalFrameEq
  rw [← lengths, Nat.min_self] at finalFrameEq
  rw [finalFrameEq] at finalSource
  exact ⟨after, finalTypes, finalLive, bound, extended, plan.typesOutside, finalWorld, finalSource⟩


#print axioms bindAll_validatedScalarParameters_protected
#print axioms FreshScalarParameterPlan.typesOutside
end Goose.Proofs.ConstructionAcceptedExecution
