import Goose.Proofs.ConstructionAcceptedEmptyParameterFrameList
import Goose.Proofs.ConstructionAcceptedParameterListProtection

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem acceptedEmptyParameterListCallBody_protected (config : EvalConfig) (accepted : AcceptedModule config)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat) (original : Context) (implementation : Impl) (values : List Value)
    (originalAt : config.module.contexts[contextId]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (parameters : ScalarParameterValues implementation 0 implementation.params.toList values)
    (world : AcceptedWorld config config.module.globals.size state ambient types live regions pending) :
    ∃ (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (after : ExecutionState)
      (finalTypes : RootTypes) (finalLive : Goose.Core.RootInst → Prop),
      let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let scopeState := ownershipResultScopeState activation implementation.body.scope activated
      frame.source.impl = implementation ∧ frame.initialized = config.module.globals.size ∧
      frame.phase = .implementation contextId ∧ frame.interpretation.environment = activation ∧
      activation.act = state.nextAct ∧ activation.scopes = [] ∧ activation.channels = [] ∧
      freshAct state = .ok activation.act { state with nextAct := state.nextAct + 1 } ∧
      freshScope activated = .ok activated.nextScope { activated with nextScope := activated.nextScope + 1 } ∧
      bindAll activation.act state.nextScope ((implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)) scopeState = .ok () after ∧
      RootTypesExtend types finalTypes ∧
      (∀ root, (∀ id, root ≠ .local activation.act state.nextScope id) → finalTypes root = types root) ∧
      AcceptedWorld config config.module.globals.size after
        (.callChannels activation [] :: ambient) finalTypes finalLive regions pending ∧
      AcceptedFrame config accepted (entryStatementsFrame config frame state.nextScope) after finalTypes ∧
      SourcePosition accepted (entryStatementsFrame config frame state.nextScope) (.statements implementation.body.stmts) := by
  obtain ⟨frame, activation, initialized, environment, act, scopes, channels, freshActStep, freshScopeStep,
      scopeWorld, scopeSource, aligned, alignedList, compatible, sameImpl, phase, visible, counter, cursor,
      origin, originAt, originImpl, activationImpl, activationVars⟩ :=
    acceptedEmptyParameterCallPushedScopeForList config accepted state ambient types live regions pending contextId original
      implementation originalAt implementationAt world
  let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
  let scopeState := ownershipResultScopeState activation implementation.body.scope activated
  let next := parameterScopeFrame frame state.nextScope
  have rootOrder : next.rootCursor.nextVar = 0 := by simp [next, parameterScopeFrame, cursor]
  have typingOrder : next.typingCounter = 0 := by simp [next, parameterScopeFrame, counter]
  have variables : next.typing.variables = implementation.vars := by
    simpa [next, parameterScopeFrame, ← sameImpl] using compatible.sourceVariables.symm
  have runtimeVariables : next.interpretation.environment.vars = implementation.vars := by
    simpa [next, parameterScopeFrame, RootInterpretation.enterScope, environment, sameImpl] using activationVars
  have nextScopes : next.interpretation.environment.scopes = (implementation.body.scope, state.nextScope) :: [] := by
    simp [next, parameterScopeFrame, RootInterpretation.enterScope, environment, sameImpl, scopes]
  have scopedWorld := scopeWorld
  rw [sameImpl] at scopedWorld scopeSource
  obtain ⟨after, finalTypes, finalLive, bound, extended, protectedTypes, afterWorld, afterSource⟩ :=
    bindAll_validatedScalarParameters_protected config accepted original.impl implementation implementationAt state.nextScope 0
      implementation.params.toList values parameters next scopeState (.callChannels activation [] :: ambient) types live regions pending []
      rootOrder typingOrder variables runtimeVariables nextScopes scopedWorld scopeSource
  have canonical := advanceParameterFrames_canonicalVisible 0 implementation.params.toList.length afterSource
  have finalSource : AcceptedFrame config accepted (parameterListBodyFrame frame state.nextScope implementation.params.size) after finalTypes := by
    have adjusted := canonical.withTypingFuel 4095
    simpa [parameterListBodyFrame, next, parameterScopeFrame, visible, List.range_eq_range'] using adjusted
  rw [alignedList] at finalSource
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
  refine ⟨frame, activation, after, finalTypes, finalLive, sameImpl, initialized, phase, environment, act, scopes, channels,
    freshActStep, freshScopeStep, ?_, extended, ?_, ?_, finalSource, position⟩
  · simpa [next, parameterScopeFrame, RootInterpretation.enterScope, environment, scopeState] using bound
  · simpa [next, parameterScopeFrame, RootInterpretation.enterScope, environment] using protectedTypes
  · simpa [next, parameterScopeFrame, RootInterpretation.enterScope, environment, initialized] using afterWorld



#print axioms acceptedEmptyParameterListCallBody_protected
end Goose.Proofs.ConstructionAcceptedExecution
