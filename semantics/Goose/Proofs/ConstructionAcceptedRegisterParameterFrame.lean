import Goose.Proofs.ConstructionAcceptedParameterChannelsFrame
import Goose.Proofs.ConstructionAcceptedParameterFrame
import Goose.Proofs.ConstructionAcceptedRegisterCall
import Goose.Proofs.ConstructionAcceptedParameterFrameList

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem acceptedRegisterParameterCallFrameForList (config : EvalConfig) (accepted : AcceptedModule config) (state : ExecutionState) (contextId : Nat) (original : Context) (implementation : Impl)
    (resultTy : Ty) (originalAt : config.module.contexts[contextId]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
 :
    ∃ frame : ConstructionSourceFrame,
      ((implementation.params.size = 1 → ∀ scopeInstance,
        { advanceLocalFrame (parameterScopeFrame frame scopeInstance) 0 with typingFuel := 4095 } =
          entryStatementsFrame config frame scopeInstance) ∧
       (implementation.params.size = 2 → ∀ scopeInstance,
        twoParameterBodyFrame frame scopeInstance = entryStatementsFrame config frame scopeInstance)) ∧
      (∀ scopeInstance, parameterListBodyFrame frame scopeInstance implementation.params.size = entryStatementsFrame config frame scopeInstance) ∧
      frame.phase = .implementation contextId ∧ frame.typing.visible = [] ∧
      frame.typing.scope = frame.source.impl.body.scope ∧ frame.typingFuel = 4096 ∧ frame.typingCounter = 0 ∧ frame.rootCursor = ⟨0, {}, []⟩ ∧
      frame.initialized = config.module.globals.size ∧
      frame.source.scopes = [] ∧ frame.source.initializing = [] ∧ frame.interpretation.environment.scopes = [] ∧
      frame.interpretation.environment.channels = [.register resultTy] ∧
      freshAct state = .ok frame.interpretation.environment.act { state with nextAct := state.nextAct + 1 } ∧
      SourceFrameCompatible accepted frame ∧ AliasComplete frame.interpretation frame.source.aliases ∧
      RootFrontier frame.interpretation (state.nextAct + 1) ∧
      LocalRootCorrespondence frame.interpretation frame.source.ctx frame.typing.visible
        { state with nextAct := state.nextAct + 1 } ∧
      ∀ fuel, ContentRootCorrespondence frame.interpretation frame.source.ctx frame.typing.visible fuel config.layout
        { state with nextAct := state.nextAct + 1 } := by
  exact acceptedParameterCallFrameForChannels config accepted state contextId original implementation [.register resultTy] originalAt implementationAt

theorem acceptedRegisterParameterCallFrameGeneral (config : EvalConfig) (accepted : AcceptedModule config) (state : ExecutionState) (contextId : Nat) (original : Context) (implementation : Impl)
    (resultTy : Ty) (originalAt : config.module.contexts[contextId]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
 :
    ∃ frame : ConstructionSourceFrame,
      ((implementation.params.size = 1 → ∀ scopeInstance,
        { advanceLocalFrame (parameterScopeFrame frame scopeInstance) 0 with typingFuel := 4095 } =
          entryStatementsFrame config frame scopeInstance) ∧
       (implementation.params.size = 2 → ∀ scopeInstance,
        twoParameterBodyFrame frame scopeInstance = entryStatementsFrame config frame scopeInstance)) ∧
      frame.phase = .implementation contextId ∧ frame.typing.visible = [] ∧
      frame.typing.scope = frame.source.impl.body.scope ∧ frame.typingFuel = 4096 ∧ frame.typingCounter = 0 ∧ frame.rootCursor = ⟨0, {}, []⟩ ∧
      frame.initialized = config.module.globals.size ∧
      frame.source.scopes = [] ∧ frame.source.initializing = [] ∧ frame.interpretation.environment.scopes = [] ∧
      frame.interpretation.environment.channels = [.register resultTy] ∧
      freshAct state = .ok frame.interpretation.environment.act { state with nextAct := state.nextAct + 1 } ∧
      SourceFrameCompatible accepted frame ∧ AliasComplete frame.interpretation frame.source.aliases ∧
      RootFrontier frame.interpretation (state.nextAct + 1) ∧
      LocalRootCorrespondence frame.interpretation frame.source.ctx frame.typing.visible
        { state with nextAct := state.nextAct + 1 } ∧
      ∀ fuel, ContentRootCorrespondence frame.interpretation frame.source.ctx frame.typing.visible fuel config.layout
        { state with nextAct := state.nextAct + 1 } := by
  obtain ⟨frame, aligned, alignedList, rest⟩ := acceptedRegisterParameterCallFrameForList config accepted state contextId original implementation resultTy originalAt implementationAt
  exact ⟨frame, aligned, rest⟩

theorem acceptedRegisterParameterCallWorldFrameForList (config : EvalConfig) (accepted : AcceptedModule config) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (liveRoots : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat) (original : Context) (implementation : Impl)
    (resultTy : Ty) (originalAt : config.module.contexts[contextId]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (world : AcceptedWorld config config.module.globals.size { state with nextAct := state.nextAct + 1 }
      ambient types liveRoots regions pending) :
    ∃ frame : ConstructionSourceFrame,
      AcceptedWorld config frame.initialized { state with nextAct := state.nextAct + 1 }
        ambient types liveRoots regions pending ∧
      AcceptedFrame config accepted frame { state with nextAct := state.nextAct + 1 } types ∧
      ((implementation.params.size = 1 → ∀ scopeInstance,
        { advanceLocalFrame (parameterScopeFrame frame scopeInstance) 0 with typingFuel := 4095 } =
          entryStatementsFrame config frame scopeInstance) ∧
       (implementation.params.size = 2 → ∀ scopeInstance,
        twoParameterBodyFrame frame scopeInstance = entryStatementsFrame config frame scopeInstance)) ∧
      (∀ scopeInstance, parameterListBodyFrame frame scopeInstance implementation.params.size = entryStatementsFrame config frame scopeInstance) ∧
      frame.phase = .implementation contextId ∧ frame.typing.visible = [] ∧
      frame.typing.scope = frame.source.impl.body.scope ∧ frame.typingFuel = 4096 ∧ frame.typingCounter = 0 ∧ frame.rootCursor = ⟨0, {}, []⟩ ∧
      frame.initialized = config.module.globals.size ∧
      frame.source.scopes = [] ∧ frame.source.initializing = [] ∧ frame.interpretation.environment.scopes = [] ∧
      frame.interpretation.environment.channels = [.register resultTy] ∧
      freshAct state = .ok frame.interpretation.environment.act { state with nextAct := state.nextAct + 1 } := by
  obtain ⟨frame, aligned, alignedList, phase, visible, typingScope, fuel, counter, cursor, initialized,
      sourceScopes, initializing, scopes, channels, allocated, compatible, aliases, frontier, direct, contents⟩ := acceptedRegisterParameterCallFrameForList config accepted state contextId original implementation resultTy originalAt implementationAt
  have framed : AcceptedFrame config accepted frame { state with nextAct := state.nextAct + 1 } types := {
    compatible := compatible
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
      rw [initialized] at future
      exact (Nat.not_lt_of_ge future bound).elim
    direct := direct
    contents := contents }
  have frameWorld : AcceptedWorld config frame.initialized { state with nextAct := state.nextAct + 1 }
      ambient types liveRoots regions pending := initialized.symm ▸ world
  exact ⟨frame, frameWorld, framed, aligned, alignedList, phase, visible, typingScope, fuel, counter, cursor, initialized,
    sourceScopes, initializing, scopes, channels, allocated⟩


theorem acceptedRegisterParameterCallWorldFrameGeneral (config : EvalConfig) (accepted : AcceptedModule config) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (liveRoots : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat) (original : Context) (implementation : Impl)
    (resultTy : Ty) (originalAt : config.module.contexts[contextId]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (world : AcceptedWorld config config.module.globals.size { state with nextAct := state.nextAct + 1 }
      ambient types liveRoots regions pending) :
    ∃ frame : ConstructionSourceFrame,
      AcceptedWorld config frame.initialized { state with nextAct := state.nextAct + 1 }
        ambient types liveRoots regions pending ∧
      AcceptedFrame config accepted frame { state with nextAct := state.nextAct + 1 } types ∧
      ((implementation.params.size = 1 → ∀ scopeInstance,
        { advanceLocalFrame (parameterScopeFrame frame scopeInstance) 0 with typingFuel := 4095 } =
          entryStatementsFrame config frame scopeInstance) ∧
       (implementation.params.size = 2 → ∀ scopeInstance,
        twoParameterBodyFrame frame scopeInstance = entryStatementsFrame config frame scopeInstance)) ∧
      frame.phase = .implementation contextId ∧ frame.typing.visible = [] ∧
      frame.typing.scope = frame.source.impl.body.scope ∧ frame.typingFuel = 4096 ∧ frame.typingCounter = 0 ∧ frame.rootCursor = ⟨0, {}, []⟩ ∧
      frame.initialized = config.module.globals.size ∧
      frame.source.scopes = [] ∧ frame.source.initializing = [] ∧ frame.interpretation.environment.scopes = [] ∧
      frame.interpretation.environment.channels = [.register resultTy] ∧
      freshAct state = .ok frame.interpretation.environment.act { state with nextAct := state.nextAct + 1 } := by
  obtain ⟨frame, frameWorld, framed, aligned, alignedList, rest⟩ := acceptedRegisterParameterCallWorldFrameForList config accepted state ambient types liveRoots regions pending contextId original implementation resultTy originalAt implementationAt world
  exact ⟨frame, frameWorld, framed, aligned, rest⟩

theorem acceptedRegisterParameterCallPushedScopeForList (config : EvalConfig) (accepted : AcceptedModule config)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat) (original : Context) (implementation : Impl)
    (resultTy : Ty) (originalAt : config.module.contexts[contextId]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (world : AcceptedWorld config config.module.globals.size state ambient types live regions pending) :
    ∃ (frame : ConstructionSourceFrame) (activation : RuntimeActivation),
      let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let scopeState := { activated with nextScope := activated.nextScope + 1 }
      let after := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let next := parameterScopeFrame frame activated.nextScope
      frame.initialized = config.module.globals.size ∧ frame.interpretation.environment = activation ∧ activation.act = state.nextAct ∧
      activation.scopes = [] ∧ activation.channels = [.register resultTy] ∧
      freshAct state = .ok activation.act { state with nextAct := state.nextAct + 1 } ∧
      freshScope activated = .ok activated.nextScope scopeState ∧
      AcceptedWorld config next.initialized after (.callChannels activation [] :: ambient) types live regions pending ∧
      AcceptedFrame config accepted next after types ∧
      ((implementation.params.size = 1 →
        { advanceLocalFrame next 0 with typingFuel := 4095 } = entryStatementsFrame config frame state.nextScope) ∧
       (implementation.params.size = 2 → twoParameterBodyFrame frame state.nextScope =
        entryStatementsFrame config frame state.nextScope)) ∧
      parameterListBodyFrame frame state.nextScope implementation.params.size = entryStatementsFrame config frame state.nextScope ∧
      SourceFrameCompatible accepted frame ∧ frame.source.impl = implementation ∧
      frame.phase = .implementation contextId ∧ frame.typing.visible = [] ∧
      frame.typingCounter = 0 ∧ frame.rootCursor = ⟨0, {}, []⟩ ∧
      ∃ original, config.module.contexts[contextId]? = some original ∧
        config.module.impls[original.impl]? = some frame.source.impl ∧
        activation.implementation = original.impl ∧ activation.vars = frame.source.impl.vars := by
  let activation : RuntimeActivation := ⟨original.impl, state.nextAct, implementation.vars, [], [.register resultTy]⟩
  let pushed := { state with activations := activation :: state.activations }
  have pushedWorld := acceptedWorld_pushRegisterActivation config config.module.globals.size state ambient types live regions pending
    activation world rfl resultTy rfl
  obtain ⟨frame, frameWorld, frameSource, aligned, alignedList, phase, visible, typingScope, fuel, counter, cursor, initialized,
    sourceScopes, initializing, scopes, channels, allocated⟩ :=
    acceptedRegisterParameterCallWorldFrameForList config accepted pushed (.callChannels activation [] :: ambient) types live regions pending
      contextId original implementation resultTy originalAt implementationAt pushedWorld
  have originFact := frameSource.compatible.origin
  unfold SourceOrigin at originFact
  rw [phase] at originFact
  obtain ⟨entry, calls, entryFound, implFound, environmentImpl, restOrigin⟩ := originFact
  have sameEntry : entry = original := Option.some.inj (entryFound.symm.trans originalAt)
  subst entry
  have sameImpl : frame.source.impl = implementation := Option.some.inj (implFound.symm.trans implementationAt)
  have identifier : frame.interpretation.environment.act = state.nextAct := by
    have exactAct : freshAct pushed = .ok state.nextAct { pushed with nextAct := pushed.nextAct + 1 } := rfl
    exact (ExecutionStep.ok.inj (allocated.symm.trans exactAct)).1
  have variables : frame.interpretation.environment.vars = implementation.vars := by
    rw [frameSource.compatible.variables, ← frameSource.compatible.sourceVariables, sameImpl]
  have environment : frame.interpretation.environment = activation := by
    cases runtime : frame.interpretation.environment with
    | mk impl act vars scopes' channels' =>
      simp only [runtime] at environmentImpl identifier variables scopes channels
      simp only [activation]
      cases environmentImpl
      cases identifier
      cases variables
      cases scopes
      cases channels
      rfl
  obtain ⟨fresh, scopeWorld, scopeSource⟩ := acceptedParameterScopeFrame config accepted frame contextId
    { pushed with nextAct := pushed.nextAct + 1 } (.callChannels activation [] :: ambient) types live regions pending
    frameWorld frameSource phase visible typingScope initializing sourceScopes scopes initialized cursor
  have scopeVisible : (parameterScopeFrame frame state.nextScope).typing.visible = [] := by
    simpa only [parameterScopeFrame] using visible
  have actualSource := scopeSource.emptyVisible_activations scopeVisible
    (({ pushed with nextAct := pushed.nextAct + 1 }).activations.map (fun (current : RuntimeActivation) =>
      if current.act == activation.act then { current with scopes := (frame.source.impl.body.scope, state.nextScope) :: activation.scopes }
      else current))
  have actualWorld := acceptedWorld_resultScope config frame.initialized
    { pushed with nextAct := pushed.nextAct + 1 } (.callChannels activation [] :: ambient) types live regions pending
    activation frame.source.impl.body.scope frameWorld
  refine ⟨frame, activation, initialized, environment, rfl, rfl, rfl, ?_, fresh, actualWorld, actualSource, ⟨(fun parameters => aligned.1 parameters state.nextScope), (fun parameters => aligned.2 parameters state.nextScope)⟩, alignedList state.nextScope, frameSource.compatible, sameImpl, phase, visible, counter, cursor, original, originalAt, ?_, rfl, ?_⟩
  · rfl
  · simpa only [sameImpl] using implementationAt
  · simp only [sameImpl, activation]



theorem acceptedRegisterParameterCallPushedScopeGeneral (config : EvalConfig) (accepted : AcceptedModule config)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat) (original : Context) (implementation : Impl)
    (resultTy : Ty) (originalAt : config.module.contexts[contextId]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (world : AcceptedWorld config config.module.globals.size state ambient types live regions pending) :
    ∃ (frame : ConstructionSourceFrame) (activation : RuntimeActivation),
      let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let scopeState := { activated with nextScope := activated.nextScope + 1 }
      let after := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let next := parameterScopeFrame frame activated.nextScope
      frame.initialized = config.module.globals.size ∧ frame.interpretation.environment = activation ∧ activation.act = state.nextAct ∧
      activation.scopes = [] ∧ activation.channels = [.register resultTy] ∧
      freshAct state = .ok activation.act { state with nextAct := state.nextAct + 1 } ∧
      freshScope activated = .ok activated.nextScope scopeState ∧
      AcceptedWorld config next.initialized after (.callChannels activation [] :: ambient) types live regions pending ∧
      AcceptedFrame config accepted next after types ∧
      ((implementation.params.size = 1 →
        { advanceLocalFrame next 0 with typingFuel := 4095 } = entryStatementsFrame config frame state.nextScope) ∧
       (implementation.params.size = 2 → twoParameterBodyFrame frame state.nextScope =
        entryStatementsFrame config frame state.nextScope)) ∧
      SourceFrameCompatible accepted frame ∧ frame.source.impl = implementation ∧
      frame.phase = .implementation contextId ∧ frame.typing.visible = [] ∧
      frame.typingCounter = 0 ∧ frame.rootCursor = ⟨0, {}, []⟩ ∧
      ∃ original, config.module.contexts[contextId]? = some original ∧
        config.module.impls[original.impl]? = some frame.source.impl ∧
        activation.implementation = original.impl ∧ activation.vars = frame.source.impl.vars := by
  obtain ⟨frame, activation, initialized, environment, act, scopes, channels, freshActStep, freshScopeStep,
    scopeWorld, scopeSource, aligned, alignedList, rest⟩ := acceptedRegisterParameterCallPushedScopeForList config accepted state ambient types live regions pending contextId original implementation resultTy originalAt implementationAt world
  exact ⟨frame, activation, initialized, environment, act, scopes, channels, freshActStep, freshScopeStep,
    scopeWorld, scopeSource, aligned, rest⟩

theorem acceptedRegisterParameterCallFrame (config : EvalConfig) (accepted : AcceptedModule config) (state : ExecutionState) (contextId : Nat) (original : Context) (implementation : Impl)
    (resultTy : Ty) (originalAt : config.module.contexts[contextId]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
 :
    ∃ frame : ConstructionSourceFrame,
      (implementation.params.size = 1 → ∀ scopeInstance,
        { advanceLocalFrame (parameterScopeFrame frame scopeInstance) 0 with typingFuel := 4095 } =
          entryStatementsFrame config frame scopeInstance) ∧
      frame.phase = .implementation contextId ∧ frame.typing.visible = [] ∧
      frame.typing.scope = frame.source.impl.body.scope ∧ frame.typingFuel = 4096 ∧ frame.typingCounter = 0 ∧ frame.rootCursor = ⟨0, {}, []⟩ ∧
      frame.initialized = config.module.globals.size ∧
      frame.source.scopes = [] ∧ frame.source.initializing = [] ∧ frame.interpretation.environment.scopes = [] ∧
      frame.interpretation.environment.channels = [.register resultTy] ∧
      freshAct state = .ok frame.interpretation.environment.act { state with nextAct := state.nextAct + 1 } ∧
      SourceFrameCompatible accepted frame ∧ AliasComplete frame.interpretation frame.source.aliases ∧
      RootFrontier frame.interpretation (state.nextAct + 1) ∧
      LocalRootCorrespondence frame.interpretation frame.source.ctx frame.typing.visible
        { state with nextAct := state.nextAct + 1 } ∧
      ∀ fuel, ContentRootCorrespondence frame.interpretation frame.source.ctx frame.typing.visible fuel config.layout
        { state with nextAct := state.nextAct + 1 } := by
  obtain ⟨frame, aligned, rest⟩ := acceptedRegisterParameterCallFrameGeneral config accepted state contextId original implementation resultTy originalAt implementationAt
  exact ⟨frame, aligned.1, rest⟩

theorem acceptedRegisterParameterCallWorldFrame (config : EvalConfig) (accepted : AcceptedModule config) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (liveRoots : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat) (original : Context) (implementation : Impl)
    (resultTy : Ty) (originalAt : config.module.contexts[contextId]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (world : AcceptedWorld config config.module.globals.size { state with nextAct := state.nextAct + 1 }
      ambient types liveRoots regions pending) :
    ∃ frame : ConstructionSourceFrame,
      AcceptedWorld config frame.initialized { state with nextAct := state.nextAct + 1 }
        ambient types liveRoots regions pending ∧
      AcceptedFrame config accepted frame { state with nextAct := state.nextAct + 1 } types ∧
      (implementation.params.size = 1 → ∀ scopeInstance,
        { advanceLocalFrame (parameterScopeFrame frame scopeInstance) 0 with typingFuel := 4095 } =
          entryStatementsFrame config frame scopeInstance) ∧
      frame.phase = .implementation contextId ∧ frame.typing.visible = [] ∧
      frame.typing.scope = frame.source.impl.body.scope ∧ frame.typingFuel = 4096 ∧ frame.typingCounter = 0 ∧ frame.rootCursor = ⟨0, {}, []⟩ ∧
      frame.initialized = config.module.globals.size ∧
      frame.source.scopes = [] ∧ frame.source.initializing = [] ∧ frame.interpretation.environment.scopes = [] ∧
      frame.interpretation.environment.channels = [.register resultTy] ∧
      freshAct state = .ok frame.interpretation.environment.act { state with nextAct := state.nextAct + 1 } := by
  obtain ⟨frame, frameWorld, framed, aligned, rest⟩ := acceptedRegisterParameterCallWorldFrameGeneral config accepted state ambient types liveRoots regions pending contextId original implementation resultTy originalAt implementationAt world
  exact ⟨frame, frameWorld, framed, aligned.1, rest⟩

theorem acceptedRegisterParameterCallPushedScope (config : EvalConfig) (accepted : AcceptedModule config)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat) (original : Context) (implementation : Impl)
    (resultTy : Ty) (originalAt : config.module.contexts[contextId]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (world : AcceptedWorld config config.module.globals.size state ambient types live regions pending) :
    ∃ (frame : ConstructionSourceFrame) (activation : RuntimeActivation),
      let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let scopeState := { activated with nextScope := activated.nextScope + 1 }
      let after := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let next := parameterScopeFrame frame activated.nextScope
      frame.initialized = config.module.globals.size ∧ frame.interpretation.environment = activation ∧ activation.act = state.nextAct ∧
      activation.scopes = [] ∧ activation.channels = [.register resultTy] ∧
      freshAct state = .ok activation.act { state with nextAct := state.nextAct + 1 } ∧
      freshScope activated = .ok activated.nextScope scopeState ∧
      AcceptedWorld config next.initialized after (.callChannels activation [] :: ambient) types live regions pending ∧
      AcceptedFrame config accepted next after types ∧
      (implementation.params.size = 1 →
        { advanceLocalFrame next 0 with typingFuel := 4095 } = entryStatementsFrame config frame state.nextScope) ∧
      SourceFrameCompatible accepted frame ∧ frame.source.impl = implementation ∧
      frame.phase = .implementation contextId ∧ frame.typing.visible = [] ∧
      frame.typingCounter = 0 ∧ frame.rootCursor = ⟨0, {}, []⟩ ∧
      ∃ original, config.module.contexts[contextId]? = some original ∧
        config.module.impls[original.impl]? = some frame.source.impl ∧
        activation.implementation = original.impl ∧ activation.vars = frame.source.impl.vars := by
  obtain ⟨frame, activation, initialized, environment, act, scopes, channels, freshActStep, freshScopeStep,
    scopeWorld, scopeSource, aligned, rest⟩ := acceptedRegisterParameterCallPushedScopeGeneral config accepted state ambient types live regions pending contextId original implementation resultTy originalAt implementationAt world
  exact ⟨frame, activation, initialized, environment, act, scopes, channels, freshActStep, freshScopeStep,
    scopeWorld, scopeSource, aligned.1, rest⟩

#print axioms acceptedRegisterParameterCallPushedScopeForList
#print axioms acceptedRegisterParameterCallPushedScopeGeneral
end Goose.Proofs.ConstructionAcceptedExecution
