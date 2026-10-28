import Goose.Proofs.ConstructionAcceptedRegisterParameterFrame
import Goose.Proofs.ConstructionAcceptedFreshness

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem acceptedRegisterParameterFrame_partial (config : EvalConfig) (accepted : AcceptedModule config)
    (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat) (original : Context) (implementation : Impl) (resultTy : Ty)
    (originalAt : config.module.contexts[contextId]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types) :
    ∃ frame : ConstructionSourceFrame,
      AcceptedWorld config frame.initialized { state with nextAct := state.nextAct + 1 } ambient types live regions pending ∧
      AcceptedFrame config accepted frame { state with nextAct := state.nextAct + 1 } types ∧
      (implementation.params.size = 1 → ∀ scopeInstance,
        { advanceLocalFrame (parameterScopeFrame frame scopeInstance) 0 with typingFuel := 4095 } =
          entryStatementsFrame config frame scopeInstance) ∧
      frame.phase = .implementation contextId ∧ frame.typing.visible = [] ∧
      frame.typing.scope = frame.source.impl.body.scope ∧ frame.typingFuel = 4096 ∧ frame.typingCounter = 0 ∧
      frame.rootCursor = ⟨0, {}, []⟩ ∧ frame.initialized = caller.initialized ∧
      frame.source.scopes = [] ∧ frame.source.initializing = [] ∧ frame.interpretation.environment.scopes = [] ∧
      frame.interpretation.environment.channels = [.register resultTy] ∧
      freshAct state = .ok frame.interpretation.environment.act { state with nextAct := state.nextAct + 1 } := by
  obtain ⟨full, aligned, alignedList, phase, visible, typingScope, fuel, counter, cursor, initialized,
      sourceScopes, initializing, scopes, channels, allocated, compatible, aliases, frontier, direct, contents⟩ :=
    acceptedRegisterParameterCallFrameForList config accepted state contextId original implementation resultTy originalAt implementationAt
  let frame := { full with initialized := caller.initialized }
  have partialCompatible : SourceFrameCompatible accepted frame := by
    refine ⟨compatible.module, compatible.rootModule, compatible.variables, compatible.sourceVariables, compatible.scopes,
      compatible.globalCount, compatible.globals, source.compatible.initialized, compatible.declarations, compatible.typingBound,
      compatible.visible, compatible.initializing, compatible.currentScope, ?_⟩
    have origin := compatible.origin
    unfold SourceOrigin at origin ⊢
    rw [phase] at origin
    simpa [frame, phase] using origin
  have framed : AcceptedFrame config accepted frame { state with nextAct := state.nextAct + 1 } types := {
    compatible := partialCompatible
    frontier := frontier
    scopeFrontier := by
      intro entry member
      rw [scopes] at member
      cases member
    initializingBefore := by
      intro id member
      rw [initializing] at member
      cases member
    aliases := aliases
    locals := by
      intro id member
      rw [visible] at member
      cases member
    localTypes := by
      intro id member
      rw [visible] at member
      cases member
    uninitializedLocals := by
      intro id _ root resolved
      have actual := rootOf_instantiates frame.interpretation id _ root resolved
      cases actual with
      | «local» id descriptor scope declared active =>
        rw [scopes] at active
        cases active
    uninitializedTypes := by
      intro id _ root resolved
      have actual := rootOf_instantiates frame.interpretation id _ root resolved
      cases actual with
      | «local» id descriptor scope declared active =>
        rw [scopes] at active
        cases active
    futureGlobals := by
      intro id future bound
      exact source.futureGlobals id future bound
    direct := direct
    contents := contents }
  have aligned' : implementation.params.size = 1 → ∀ scopeInstance,
      { advanceLocalFrame (parameterScopeFrame frame scopeInstance) 0 with typingFuel := 4095 } =
        entryStatementsFrame config frame scopeInstance := by
    intro one scopeInstance
    have equality := congrArg (fun current : ConstructionSourceFrame => { current with initialized := caller.initialized })
      (aligned.1 one scopeInstance)
    simpa [frame, parameterScopeFrame, advanceLocalFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using equality
  exact ⟨frame, (freshAct_acceptedWorld config caller.initialized state ambient types live world).2, framed, aligned', phase, visible,
    typingScope, fuel, counter, cursor, rfl, sourceScopes, initializing, scopes, channels, allocated⟩

#print axioms acceptedRegisterParameterFrame_partial
end Goose.Proofs.ConstructionAcceptedExecution
