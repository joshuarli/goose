import Goose.Proofs.ConstructionAcceptedPartialRegisterParameterFrame
import Goose.Proofs.ConstructionAcceptedEntryCall
import Goose.Proofs.ConstructionAcceptedRegisterCall

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem acceptedRegisterParameterPushedScope_partial (config : EvalConfig) (accepted : AcceptedModule config)
    (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat) (original : Context) (implementation : Impl) (resultTy : Ty)
    (originalAt : config.module.contexts[contextId]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types) :
    ∃ (frame : ConstructionSourceFrame) (activation : RuntimeActivation),
      let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let scopeState := { activated with nextScope := activated.nextScope + 1 }
      let after := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let next := parameterScopeFrame frame activated.nextScope
      frame.initialized = caller.initialized ∧ frame.interpretation.environment = activation ∧ activation.act = state.nextAct ∧
      activation.scopes = [] ∧ activation.channels = [.register resultTy] ∧
      freshAct state = .ok activation.act { state with nextAct := state.nextAct + 1 } ∧
      freshScope activated = .ok activated.nextScope scopeState ∧
      AcceptedWorld config next.initialized after (.callChannels activation [] :: ambient) types live regions pending ∧
      AcceptedFrame config accepted next after types ∧
      (implementation.params.size = 1 → { advanceLocalFrame next 0 with typingFuel := 4095 } = entryStatementsFrame config frame state.nextScope) ∧
      SourceFrameCompatible accepted frame ∧ frame.source.impl = implementation ∧
      frame.phase = .implementation contextId ∧ frame.typing.visible = [] ∧
      frame.typingCounter = 0 ∧ frame.rootCursor = ⟨0, {}, []⟩ ∧
      activation.implementation = original.impl ∧ activation.vars = implementation.vars := by
  obtain ⟨frame, frameWorld, frameSource, aligned, phase, visible, typingScope, fuel, counter, cursor, initialized,
      sourceScopes, initializing, scopes, channels, allocated⟩ :=
    acceptedRegisterParameterFrame_partial config accepted caller state ambient types live regions pending contextId original implementation
      resultTy originalAt implementationAt world source
  have originFact := frameSource.compatible.origin
  unfold SourceOrigin at originFact
  rw [phase] at originFact
  obtain ⟨entry, calls, entryFound, implFound, environmentImpl, restOrigin⟩ := originFact
  have sameEntry : entry = original := Option.some.inj (entryFound.symm.trans originalAt)
  subst entry
  have sameImpl : frame.source.impl = implementation := Option.some.inj (implFound.symm.trans implementationAt)
  have identifier : frame.interpretation.environment.act = state.nextAct := by
    have exactAct : freshAct state = .ok state.nextAct { state with nextAct := state.nextAct + 1 } := rfl
    exact (ExecutionStep.ok.inj (allocated.symm.trans exactAct)).1
  have variables : frame.interpretation.environment.vars = implementation.vars := by
    rw [frameSource.compatible.variables, ← frameSource.compatible.sourceVariables, sameImpl]
  let activation := frame.interpretation.environment
  let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
  have pushedWorld : AcceptedWorld config frame.initialized activated (.callChannels activation [] :: ambient) types live regions pending := by
    rw [initialized]
    exact acceptedWorld_pushRegisterActivation config caller.initialized state ambient types live regions pending activation world identifier resultTy channels
  have pushedSource : AcceptedFrame config accepted frame activated types := by
    exact frameSource.emptyVisible_activations visible (activation :: state.activations)
  obtain ⟨fresh, scopeWorld, scopeSource⟩ := acceptedParameterScopeFrame_partial config accepted frame contextId activated
    (.callChannels activation [] :: ambient) types live regions pending pushedWorld pushedSource phase visible typingScope
    initializing sourceScopes scopes cursor
  have scopeVisible : (parameterScopeFrame frame state.nextScope).typing.visible = [] := by
    simpa only [parameterScopeFrame] using visible
  have actualSource := scopeSource.emptyVisible_activations scopeVisible
    (activated.activations.map (fun (current : RuntimeActivation) =>
      if current.act == activation.act then { current with scopes := (frame.source.impl.body.scope, state.nextScope) :: activation.scopes }
      else current))
  have actualWorld := acceptedWorld_resultScope config frame.initialized activated (.callChannels activation [] :: ambient) types live
    regions pending activation frame.source.impl.body.scope pushedWorld
  refine ⟨frame, activation, initialized, rfl, identifier, scopes, channels, allocated, fresh, actualWorld, actualSource,
    (fun one => aligned one state.nextScope), frameSource.compatible, sameImpl, phase, visible, counter, cursor, environmentImpl, variables⟩

#print axioms acceptedRegisterParameterPushedScope_partial
end Goose.Proofs.ConstructionAcceptedExecution
