import Goose.Proofs.ConstructionAcceptedEmptyCallFrame
import Goose.Proofs.ConstructionAcceptedScalarBinding

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

def parameterScopeFrame (frame : ConstructionSourceFrame) (scopeInstance : Nat) : ConstructionSourceFrame :=
  { frame with
    source := { frame.source with scopes := frame.source.impl.body.scope :: frame.source.scopes }
    interpretation := frame.interpretation.enterScope frame.source.impl.body.scope scopeInstance }

theorem acceptedParameterCallFrame (config : EvalConfig) (accepted : AcceptedModule config) (state : ExecutionState) (contextId : Nat) (original : Context) (implementation : Impl)
    (originalAt : config.module.contexts[contextId]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
 :
    ∃ frame : ConstructionSourceFrame,
      (implementation.params.size = 1 → implementation.results = #[] → ∀ scopeInstance,
        { advanceLocalFrame (parameterScopeFrame frame scopeInstance) 0 with typingFuel := 4095 } =
          entryStatementsFrame config frame scopeInstance) ∧
      frame.phase = .implementation contextId ∧ frame.typing.visible = [] ∧
      frame.typing.scope = frame.source.impl.body.scope ∧ frame.typingFuel = 4096 ∧ frame.typingCounter = 0 ∧ frame.rootCursor = ⟨0, {}, []⟩ ∧
      frame.initialized = config.module.globals.size ∧
      frame.source.scopes = [] ∧ frame.source.initializing = [] ∧ frame.interpretation.environment.scopes = [] ∧
      frame.interpretation.environment.channels = [] ∧
      freshAct state = .ok frame.interpretation.environment.act { state with nextAct := state.nextAct + 1 } ∧
      SourceFrameCompatible accepted frame ∧ AliasComplete frame.interpretation frame.source.aliases ∧
      RootFrontier frame.interpretation (state.nextAct + 1) ∧
      LocalRootCorrespondence frame.interpretation frame.source.ctx frame.typing.visible
        { state with nextAct := state.nextAct + 1 } ∧
      ∀ fuel, ContentRootCorrespondence frame.interpretation frame.source.ctx frame.typing.visible fuel config.layout
        { state with nextAct := state.nextAct + 1 } := by
  have member : (original, contextId) ∈ config.module.contexts.toList.zipIdx := by
    apply List.mem_of_getElem? (i := contextId)
    simp only [List.getElem?_zipIdx, Array.getElem?_toList, originalAt, Option.map_some, Nat.zero_add]
  obtain ⟨calls, contextFacts, callsCovered⟩ := (Classical.choose_spec accepted.roots).2.1
    (original, contextId) member
  obtain ⟨escaping, names, contextFactsAt⟩ := contextFacts
  obtain ⟨bodyImplementation, bodyContext, targetEscapes, roots, rootAfter,
      bodyImplementationAt, closed, targetsChecked, rootsChecked, _bodyCallsIncluded⟩ :=
    contextRootFactsAt_bodyRoots config.module original accepted.aliases[contextId]! calls
      escaping names contextFactsAt
  have same : bodyImplementation = implementation := by
    simpa only [implementationAt, Option.some.injEq] using bodyImplementationAt.symm
  subst bodyImplementation
  let environment : RuntimeActivation := ⟨original.impl, state.nextAct, implementation.vars, [], []⟩
  let interpretation := EntryInterpretation environment config.module.globals.size
  let typing : TypingEnv := {
    module := config.module
    implementation := some implementation
    variables := implementation.vars
    visible := []
    scope := implementation.body.scope
    loops := 0
    use := .ordinary
    request := .value
    resultRequests := []
    globalLimit := config.module.globals.size }
  let source : PEnv := {
    mod := config.module
    impl := implementation
    ctx := bodyContext
    scopes := []
    escaping := escaping
    targetEscapes := targetEscapes
    aliases := accepted.aliases[contextId]!
    calleeNames := names }
  let frame : ConstructionSourceFrame := {
    phase := .implementation contextId
    typing := typing
    source := source
    interpretation := interpretation
    initialized := config.module.globals.size
    typingFuel := 4096
    typingCounter := 0
    rootCursor := ⟨0, {}, []⟩ }
  have compatible : SourceFrameCompatible accepted frame := {
    module := rfl
    rootModule := rfl
    variables := rfl
    sourceVariables := rfl
    scopes := rfl
    globalCount := rfl
    globals := Nat.le_refl _
    initialized := Nat.le_refl _
    declarations := Nat.le_refl _
    typingBound := Nat.zero_le _
    visible := by intro id absent; cases absent
    initializing := by intro id absent; cases absent
    currentScope := by intro scope rest absent; cases absent
    origin := by
      refine ⟨original, calls, originalAt, implementationAt, rfl, rfl, closed, rfl, contextFactsAt, callsCovered,
        targetsChecked, roots, rootAfter, ?_⟩
      simpa only [frame, source] using rootsChecked }
  have aliases : AliasComplete interpretation source.aliases :=
    aliasComplete_mono interpretation [] source.aliases (entry_aliasComplete environment config.module.globals.size)
      (by intro pair absent; cases absent)
  have frontier : RootFrontier interpretation (state.nextAct + 1) :=
    ⟨Nat.lt_succ_self _, fun _ _ _ _ impossible => impossible.elim⟩
  have locals := localRootCorrespondence_empty interpretation bodyContext { state with nextAct := state.nextAct + 1 }
  have contents : ∀ fuel, ContentRootCorrespondence interpretation bodyContext [] fuel config.layout
      { state with nextAct := state.nextAct + 1 } := by
    intro fuel id absent
    cases absent
  have aligned : implementation.params.size = 1 → implementation.results = #[] → ∀ scopeInstance,
      { advanceLocalFrame (parameterScopeFrame frame scopeInstance) 0 with typingFuel := 4095 } =
        entryStatementsFrame config frame scopeInstance := by
    intro parameters results scopeInstance
    simp [frame, typing, source, parameterScopeFrame, advanceLocalFrame, entryStatementsFrame,
      blockStatementsFrame, implementationBodyFrame, parameters, results, List.range]
    rfl
  exact ⟨frame, aligned, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    compatible, aliases, frontier, locals, contents⟩

theorem acceptedParameterCallWorldFrame (config : EvalConfig) (accepted : AcceptedModule config) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (liveRoots : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat) (original : Context) (implementation : Impl)
    (originalAt : config.module.contexts[contextId]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (world : AcceptedWorld config config.module.globals.size { state with nextAct := state.nextAct + 1 }
      ambient types liveRoots regions pending) :
    ∃ frame : ConstructionSourceFrame,
      AcceptedWorld config frame.initialized { state with nextAct := state.nextAct + 1 }
        ambient types liveRoots regions pending ∧
      AcceptedFrame config accepted frame { state with nextAct := state.nextAct + 1 } types ∧
      (implementation.params.size = 1 → implementation.results = #[] → ∀ scopeInstance,
        { advanceLocalFrame (parameterScopeFrame frame scopeInstance) 0 with typingFuel := 4095 } =
          entryStatementsFrame config frame scopeInstance) ∧
      frame.phase = .implementation contextId ∧ frame.typing.visible = [] ∧
      frame.typing.scope = frame.source.impl.body.scope ∧ frame.typingFuel = 4096 ∧ frame.typingCounter = 0 ∧ frame.rootCursor = ⟨0, {}, []⟩ ∧
      frame.initialized = config.module.globals.size ∧
      frame.source.scopes = [] ∧ frame.source.initializing = [] ∧ frame.interpretation.environment.scopes = [] ∧
      frame.interpretation.environment.channels = [] ∧
      freshAct state = .ok frame.interpretation.environment.act { state with nextAct := state.nextAct + 1 } := by
  obtain ⟨frame, aligned, phase, visible, typingScope, fuel, counter, cursor, initialized,
      sourceScopes, initializing, scopes, channels, allocated, compatible, aliases, frontier, direct, contents⟩ := acceptedParameterCallFrame config accepted state contextId original implementation originalAt implementationAt
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
  exact ⟨frame, frameWorld, framed, aligned, phase, visible, typingScope, fuel, counter, cursor, initialized,
    sourceScopes, initializing, scopes, channels, allocated⟩


theorem acceptedParameterScopeFrame_partial (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (contextId : Nat) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (phase : frame.phase = .implementation contextId)
    (visible : frame.typing.visible = []) (typingScope : frame.typing.scope = frame.source.impl.body.scope)
    (initializing : frame.source.initializing = [])
    (sourceScopes : frame.source.scopes = [])
    (scopes : frame.interpretation.environment.scopes = [])
    (cursor : frame.rootCursor = ⟨0, {}, []⟩) :
    let next := parameterScopeFrame frame state.nextScope
    let after := { state with nextScope := state.nextScope + 1 }
    freshScope state = .ok state.nextScope after ∧
    AcceptedWorld config next.initialized after ambient types live regions pending ∧
    AcceptedFrame config accepted next after types := by
  let scope := frame.source.impl.body.scope
  let after := { state with nextScope := state.nextScope + 1 }
  let interpretation := frame.interpretation.enterScope scope state.nextScope
  let next := parameterScopeFrame frame state.nextScope
  have scopeWorld := (freshScope_acceptedWorld config frame.initialized state ambient types live world).2
  have frontier : RootFrontier interpretation after.nextAct := by
    exact rootFrontier_enterScope frame.interpretation scope state.nextScope state.nextAct source.frontier
  have aliases : AliasComplete interpretation frame.source.aliases :=
    aliasComplete_enterScope frame.interpretation frame.source.aliases scope state.nextScope state.nextAct source.frontier source.aliases
  have emptyTypes : ∀ id root, rootOf interpretation.environment id after = .ok root after → types root = none := by
    intro id root resolved
    apply source.enterScope_uninitializedTypes world scope id ?_ root resolved
    left
    simp only [cursor]
    exact Nat.zero_le _
  have compatible : SourceFrameCompatible accepted next := by
    refine ⟨source.compatible.module, source.compatible.rootModule, ?_, source.compatible.sourceVariables,
      ?_, source.compatible.globalCount, source.compatible.globals, source.compatible.initialized,
      source.compatible.declarations, source.compatible.typingBound, source.compatible.visible,
      source.compatible.initializing, ?_, ?_⟩
    · simpa [next, parameterScopeFrame, RootInterpretation.enterScope] using source.compatible.variables
    · simp [next, parameterScopeFrame, RootInterpretation.enterScope, scopes, sourceScopes]
    · intro current rest same
      simp only [next, parameterScopeFrame, List.cons.injEq] at same
      exact typingScope.trans same.1
    · have origin := source.compatible.origin
      unfold SourceOrigin at origin ⊢
      rw [phase] at origin
      simp only [next, parameterScopeFrame, RootInterpretation.enterScope, phase]
      obtain ⟨original, calls, found, implementation, environment, typing, remaining⟩ := origin
      exact ⟨original, calls, found, implementation, environment, typing, remaining⟩
  have framed : AcceptedFrame config accepted next after types := by
    refine ⟨compatible, frontier, ?_, ?_, aliases, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro entry member
      simp only [next, parameterScopeFrame, RootInterpretation.enterScope, scopes, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst entry
      exact Nat.lt_succ_self _
    · intro id member
      simp only [next, parameterScopeFrame, initializing, List.not_mem_nil] at member
    · intro id member
      simp only [next, parameterScopeFrame, visible, List.not_mem_nil] at member
    · intro id member
      simp only [next, parameterScopeFrame, visible, List.not_mem_nil] at member
    · intro id _ root resolved
      have absent := emptyTypes id root resolved
      constructor
      · cases present : state.objects.lookup root with
        | none => rfl
        | some value =>
          obtain ⟨ty, typed⟩ := world.objectsRegistered root value present
          rw [absent] at typed
          cases typed
      · cases present : state.objectOrdinals.lookup root with
        | none => rfl
        | some value =>
          obtain ⟨ty, typed⟩ := world.ordinalsRegistered root value present
          rw [absent] at typed
          cases typed
    · intro id _ root resolved
      exact emptyTypes id root resolved
    · intro id future bound
      exact source.futureGlobals id future bound
    · intro id member
      simp only [next, parameterScopeFrame, visible, List.not_mem_nil] at member
    · intro fuel id member
      simp only [next, parameterScopeFrame, visible, List.not_mem_nil] at member
  exact ⟨rfl, scopeWorld, framed⟩

theorem acceptedParameterScopeFrame (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (contextId : Nat) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (phase : frame.phase = .implementation contextId)
    (visible : frame.typing.visible = []) (typingScope : frame.typing.scope = frame.source.impl.body.scope)
    (initializing : frame.source.initializing = [])
    (sourceScopes : frame.source.scopes = [])
    (scopes : frame.interpretation.environment.scopes = []) (initialized : frame.initialized = config.module.globals.size)
    (cursor : frame.rootCursor = ⟨0, {}, []⟩) :
    let next := parameterScopeFrame frame state.nextScope
    let after := { state with nextScope := state.nextScope + 1 }
    freshScope state = .ok state.nextScope after ∧
    AcceptedWorld config next.initialized after ambient types live regions pending ∧
    AcceptedFrame config accepted next after types := by
  exact acceptedParameterScopeFrame_partial config accepted frame contextId state ambient types live regions pending world source phase
    visible typingScope initializing sourceScopes scopes cursor

theorem acceptedParameterCallPushedScope (config : EvalConfig) (accepted : AcceptedModule config)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat) (original : Context) (implementation : Impl)
    (originalAt : config.module.contexts[contextId]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (world : AcceptedWorld config config.module.globals.size state ambient types live regions pending) :
    ∃ (frame : ConstructionSourceFrame) (activation : RuntimeActivation),
      let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let scopeState := { activated with nextScope := activated.nextScope + 1 }
      let after := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let next := parameterScopeFrame frame activated.nextScope
      frame.initialized = config.module.globals.size ∧ frame.interpretation.environment = activation ∧ activation.act = state.nextAct ∧
      activation.scopes = [] ∧ activation.channels = [] ∧
      freshAct state = .ok activation.act { state with nextAct := state.nextAct + 1 } ∧
      freshScope activated = .ok activated.nextScope scopeState ∧
      AcceptedWorld config next.initialized after (.callChannels activation [] :: ambient) types live regions pending ∧
      AcceptedFrame config accepted next after types ∧
      (implementation.params.size = 1 → implementation.results = #[] →
        { advanceLocalFrame next 0 with typingFuel := 4095 } = entryStatementsFrame config frame state.nextScope) ∧
      SourceFrameCompatible accepted frame ∧ frame.source.impl = implementation ∧
      frame.phase = .implementation contextId ∧ frame.typing.visible = [] ∧
      frame.typingCounter = 0 ∧ frame.rootCursor = ⟨0, {}, []⟩ ∧
      ∃ original, config.module.contexts[contextId]? = some original ∧
        config.module.impls[original.impl]? = some frame.source.impl ∧
        activation.implementation = original.impl ∧ activation.vars = frame.source.impl.vars := by
  let activation : RuntimeActivation := ⟨original.impl, state.nextAct, implementation.vars, [], []⟩
  let pushed := { state with activations := activation :: state.activations }
  have pushedWorld := acceptedWorld_pushEmptyActivation config config.module.globals.size state ambient types live regions pending
    activation world rfl rfl
  obtain ⟨frame, frameWorld, frameSource, aligned, phase, visible, typingScope, fuel, counter, cursor, initialized,
    sourceScopes, initializing, scopes, channels, allocated⟩ :=
    acceptedParameterCallWorldFrame config accepted pushed (.callChannels activation [] :: ambient) types live regions pending
      contextId original implementation originalAt implementationAt pushedWorld
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
  refine ⟨frame, activation, initialized, environment, rfl, rfl, rfl, ?_, fresh, actualWorld, actualSource, (fun parameters results => aligned parameters results state.nextScope), frameSource.compatible, sameImpl, phase, visible, counter, cursor, original, originalAt, ?_, rfl, ?_⟩
  · rfl
  · simpa only [sameImpl] using implementationAt
  · simp only [sameImpl, activation]


#print axioms acceptedParameterCallPushedScope
#print axioms acceptedParameterScopeFrame
#print axioms acceptedParameterCallWorldFrame
#print axioms acceptedParameterCallFrame
#print axioms acceptedParameterScopeFrame_partial
end Goose.Proofs.ConstructionAcceptedExecution
