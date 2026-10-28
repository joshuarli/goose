import Goose.Proofs.ConstructionAcceptedRegisterParameterCall
import Goose.Proofs.ConstructionAcceptedTwoScalarBinding
import Goose.Proofs.ConstructionAcceptedVisibleFrame

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem acceptedRegisterTwoParameterCallBody (config : EvalConfig) (accepted : AcceptedModule config)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat) (original : Context) (implementation : Impl)
    (first second : Param) (firstDescriptor secondDescriptor : LocalVar) (firstValue secondValue : Value) (resultTy : Ty)
    (originalAt : config.module.contexts[contextId]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (parameters : implementation.params = #[first, second])
    (firstDeclared : implementation.vars[0]? = some firstDescriptor)
    (secondDeclared : implementation.vars[1]? = some secondDescriptor)
    (firstScalar : (∃ intTy, firstDescriptor.ty = .int intTy) ∨ firstDescriptor.ty = .bool)
    (secondScalar : (∃ intTy, secondDescriptor.ty = .int intTy) ∨ secondDescriptor.ty = .bool)
    (firstRepresented : ValueRepresentation firstDescriptor.ty firstValue)
    (secondRepresented : ValueRepresentation secondDescriptor.ty secondValue)
    (firstPointers : PointerTypedValue types firstDescriptor.ty firstValue)
    (secondPointers : PointerTypedValue types secondDescriptor.ty secondValue)
    (world : AcceptedWorld config config.module.globals.size state ambient types live regions pending) :
    ∃ (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (after : ExecutionState),
      let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let scopeState := ownershipResultScopeState activation implementation.body.scope activated
      let rootFirst := Goose.Core.RootInst.local activation.act state.nextScope 0
      let rootSecond := Goose.Core.RootInst.local activation.act state.nextScope 1
      let afterTypes := registerRootType (registerRootType types rootFirst firstDescriptor.ty) rootSecond secondDescriptor.ty
      frame.source.impl = implementation ∧ frame.initialized = config.module.globals.size ∧
      frame.phase = .implementation contextId ∧ frame.interpretation.environment = activation ∧
      activation.act = state.nextAct ∧ activation.scopes = [] ∧ activation.channels = [.register resultTy] ∧
      freshAct state = .ok activation.act { state with nextAct := state.nextAct + 1 } ∧
      freshScope activated = .ok activated.nextScope { activated with nextScope := activated.nextScope + 1 } ∧
      bindAll activation.act state.nextScope [(first.var, firstValue), (second.var, secondValue)] scopeState = .ok () after ∧
      AcceptedWorld config config.module.globals.size after (.callChannels activation [] :: ambient) afterTypes
        (fun other => other = rootSecond ∨ other = rootFirst ∨ live other) regions pending ∧
      AcceptedFrame config accepted (entryStatementsFrame config frame state.nextScope) after afterTypes ∧
      SourcePosition accepted (entryStatementsFrame config frame state.nextScope) (.statements implementation.body.stmts) := by
  obtain ⟨frame, activation, initialized, environment, act, scopes, channels, freshActStep, freshScopeStep,
      scopeWorld, scopeSource, aligned, compatible, sameImpl, phase, visible, counter, cursor,
      origin, originAt, originImpl, activationImpl, activationVars⟩ :=
    acceptedRegisterParameterCallPushedScopeGeneral config accepted state ambient types live regions pending contextId original
      implementation resultTy originalAt implementationAt world
  have firstAt : implementation.params[0]? = some first := by simp [parameters]
  have secondAt : implementation.params[1]? = some second := by simp [parameters]
  have firstId := validated_parameter_variable config.module original.impl implementation 0 first
    accepted.accepted implementationAt firstAt
  have secondId := validated_parameter_variable config.module original.impl implementation 1 second
    accepted.accepted implementationAt secondAt
  let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
  let scopeState := ownershipResultScopeState activation implementation.body.scope activated
  have resolved (id : Nat) (parameter : Param) (parameterAt : implementation.params[id]? = some parameter)
      (parameterId : parameter.var = id) :
      rootOf (parameterScopeFrame frame state.nextScope).interpretation.environment id scopeState =
        .ok (.local (parameterScopeFrame frame state.nextScope).interpretation.environment.act state.nextScope id) scopeState := by
    have step := (validated_parameter_initialRoot config.module original.impl implementation id parameter
      frame.interpretation activated accepted.accepted implementationAt parameterAt (by simpa [environment, sameImpl] using activationVars)).2
    have transferred := rootOf_transfer (frame.interpretation.enterScope implementation.body.scope state.nextScope) id
      { activated with nextScope := activated.nextScope + 1 } scopeState
      (.local activation.act state.nextScope id) (by simpa [parameterId, environment] using step)
    simpa [parameterScopeFrame, RootInterpretation.enterScope, sameImpl, environment] using transferred
  have typedFirst : (parameterScopeFrame frame state.nextScope).typing.variables[0]? = some firstDescriptor := by
    simpa [parameterScopeFrame, ← compatible.sourceVariables, sameImpl] using firstDeclared
  have typedSecond : (advanceLocalFrame (parameterScopeFrame frame state.nextScope) 0).typing.variables[1]? = some secondDescriptor := by
    simpa [advanceLocalFrame, parameterScopeFrame, ← compatible.sourceVariables, sameImpl] using secondDeclared
  have scopedWorld := scopeWorld
  rw [sameImpl] at scopedWorld scopeSource
  obtain ⟨after, bound, afterWorld, afterSource⟩ := bindAll_two_freshScalars_accepted scopedWorld scopeSource
    0 1 firstDescriptor secondDescriptor state.nextScope firstValue secondValue
    (by simp [parameterScopeFrame, cursor]) (by simp [parameterScopeFrame, counter]) typedFirst (resolved 0 first firstAt firstId)
    firstScalar firstRepresented firstPointers
    (by simp [advanceLocalFrame, parameterScopeFrame, cursor]) (by simp [advanceLocalFrame, parameterScopeFrame, counter])
    typedSecond (resolved 1 second secondAt secondId) secondScalar secondRepresented secondPointers
  have normalized := afterSource.withVisibleSubset [0, 1] (by
    intro id member
    simp only [advanceLocalFrame, parameterScopeFrame, visible, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    rcases member with same | same <;> simp [same])
  have finalSource := normalized.withTypingFuel 4095
  have finalSource' := finalSource
  change AcceptedFrame config accepted (twoParameterBodyFrame frame state.nextScope) after _ at finalSource'
  rw [aligned.2 (by simp [parameters])] at finalSource'
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
  refine ⟨frame, activation, after, sameImpl, initialized, phase, environment, act, scopes, channels, freshActStep, freshScopeStep, ?_, ?_, ?_, position⟩
  · simpa [parameterScopeFrame, RootInterpretation.enterScope, environment, firstId, secondId, scopeState] using bound
  · simpa [parameterScopeFrame, RootInterpretation.enterScope, environment, initialized] using afterWorld
  · simpa [parameterScopeFrame, RootInterpretation.enterScope, environment] using finalSource'

#print axioms acceptedRegisterTwoParameterCallBody
end Goose.Proofs.ConstructionAcceptedExecution
