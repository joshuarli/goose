import Goose.Proofs.ConstructionAcceptedPartialRegisterParameterScope
import Goose.Proofs.ConstructionAcceptedScalarParameter
import Goose.Proofs.ConstructionRootCorrespondenceScopes

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem acceptedRegisterParameterCallBody_partial (config : EvalConfig) (accepted : AcceptedModule config)
    (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat) (original : Context) (implementation : Impl) (parameter : Param) (descriptor : LocalVar) (value : Value) (resultTy : Ty)
    (originalAt : config.module.contexts[contextId]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (parameters : implementation.params = #[parameter])
    (declared : implementation.vars[0]? = some descriptor)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (represented : ValueRepresentation descriptor.ty value) (pointers : PointerTypedValue types descriptor.ty value)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types) :
    ∃ (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (after : ExecutionState),
      let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let scopeState := ownershipResultScopeState activation implementation.body.scope activated
      let root := Goose.Core.RootInst.local activation.act state.nextScope 0
      frame.source.impl = implementation ∧ frame.initialized = caller.initialized ∧ frame.phase = .implementation contextId ∧ frame.interpretation.environment = activation ∧
      activation.act = state.nextAct ∧ activation.scopes = [] ∧ activation.channels = [.register resultTy] ∧
      freshAct state = .ok activation.act { state with nextAct := state.nextAct + 1 } ∧
      freshScope activated = .ok activated.nextScope { activated with nextScope := activated.nextScope + 1 } ∧
      bindAll activation.act state.nextScope [(parameter.var, value)] scopeState = .ok () after ∧
      RootTypesExtend types (registerRootType types root descriptor.ty) ∧
      AcceptedWorld config caller.initialized after (.callChannels activation [] :: ambient)
        (registerRootType types root descriptor.ty) (fun other => other = root ∨ live other) regions pending ∧
      AcceptedFrame config accepted (entryStatementsFrame config frame state.nextScope) after
        (registerRootType types root descriptor.ty) ∧
      SourcePosition accepted (entryStatementsFrame config frame state.nextScope) (.statements implementation.body.stmts) := by
  obtain ⟨frame, activation, initialized, environment, act, scopes, channels, freshActStep, freshScopeStep,
      scopeWorld, scopeSource, aligned, compatible, sameImpl, phase, visible, counter, cursor, activationImpl, activationVars⟩ :=
    acceptedRegisterParameterPushedScope_partial config accepted caller state ambient types live regions pending contextId original
      implementation resultTy originalAt implementationAt world source
  have parameterAt : implementation.params[0]? = some parameter := by simp [parameters]
  have parameterId := validated_parameter_variable config.module original.impl implementation 0 parameter
    accepted.accepted implementationAt parameterAt
  have typed : (parameterScopeFrame frame state.nextScope).typing.variables[0]? = some descriptor := by
    simpa [parameterScopeFrame, ← compatible.sourceVariables, sameImpl] using declared
  let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
  let scopeState := ownershipResultScopeState activation implementation.body.scope activated
  have rootStep : rootOf (parameterScopeFrame frame state.nextScope).interpretation.environment 0 scopeState =
      .ok (.local activation.act state.nextScope 0) scopeState := by
    have step := (validated_parameter_initialRoot config.module original.impl implementation 0 parameter
      frame.interpretation activated accepted.accepted implementationAt parameterAt (by simpa [environment, sameImpl] using activationVars)).2
    have transferred := rootOf_transfer (frame.interpretation.enterScope implementation.body.scope state.nextScope) 0
      { activated with nextScope := activated.nextScope + 1 } scopeState
      (.local activation.act state.nextScope 0) (by simpa [parameterId, environment] using step)
    simpa [parameterScopeFrame, sameImpl] using transferred
  have rootStep' : rootOf (parameterScopeFrame frame state.nextScope).interpretation.environment 0 scopeState =
      .ok (.local (parameterScopeFrame frame state.nextScope).interpretation.environment.act state.nextScope 0) scopeState := by
    simpa [parameterScopeFrame, RootInterpretation.enterScope, environment] using rootStep
  have rootOrder : 0 = (parameterScopeFrame frame state.nextScope).rootCursor.nextVar := by simp [parameterScopeFrame, cursor]
  have typingOrder : 0 = (parameterScopeFrame frame state.nextScope).typingCounter := by simp [parameterScopeFrame, counter]
  have scopedWorld := scopeWorld
  rw [sameImpl] at scopedWorld scopeSource
  obtain ⟨after, bound, extended, afterWorld, afterSource⟩ := bindAll_freshScalar_accepted scopedWorld scopeSource
    0 descriptor state.nextScope value rootOrder typingOrder typed rootStep' scalar represented pointers
  have aligned' := aligned (by simp [parameters])
  have finalSource := afterSource.withTypingFuel 4095
  rw [aligned'] at finalSource
  have bodyPosition : SourcePosition accepted (implementationBodyFrame config frame) (.block frame.source.impl.body) :=
    .implementationBody frame contextId phase compatible
  have statementsPosition : SourcePosition accepted
      (blockStatementsFrame (implementationBodyFrame config frame) frame.source.impl.body.scope 4095)
      (.statements frame.source.impl.body.stmts) := by
    cases body : frame.source.impl.body with
    | mk scope statements tail =>
      rw [body] at bodyPosition
      simpa only [body, Block.scope, Block.stmts, implementationBodyFrame] using
        bodyPosition.block_statements accepted (implementationBodyFrame config frame) scope 4095 statements tail rfl
  have position : SourcePosition accepted (entryStatementsFrame config frame state.nextScope)
      (.statements implementation.body.stmts) := by
    have position := SourcePosition.instantiate statementsPosition
      (frame.interpretation.enterScope frame.source.impl.body.scope state.nextScope) frame.initialized
    simpa [entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, sameImpl] using position
  refine ⟨frame, activation, after, sameImpl, initialized, phase, environment, act, scopes, channels, freshActStep, freshScopeStep, ?_, ?_, ?_, ?_, position⟩
  · simpa [parameterScopeFrame, RootInterpretation.enterScope, environment, parameterId, scopeState] using bound
  · simpa [parameterScopeFrame, RootInterpretation.enterScope, environment] using extended
  · simpa [parameterScopeFrame, RootInterpretation.enterScope, environment, initialized] using afterWorld
  · simpa [parameterScopeFrame, RootInterpretation.enterScope, environment] using finalSource

#print axioms acceptedRegisterParameterCallBody_partial
end Goose.Proofs.ConstructionAcceptedExecution
