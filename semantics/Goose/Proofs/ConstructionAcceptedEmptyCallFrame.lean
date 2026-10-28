import Goose.Proofs.ConstructionRootCorrespondenceAcceptedEntryState
import Goose.Proofs.ConstructionAcceptedEntryCall

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem acceptedEmptyCallFrame (config : EvalConfig) (accepted : AcceptedModule config) (state : ExecutionState) (contextId : Nat) (original : Context) (implementation : Impl)
    (originalAt : config.module.contexts[contextId]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (parametersEmpty : implementation.params = #[]) (resultsEmpty : implementation.results = #[]) :
    ∃ frame : ConstructionSourceFrame,
      frame.phase = .implementation contextId ∧ frame.typing.visible = [] ∧
      frame.typingFuel = 4096 ∧ frame.typingCounter = 0 ∧ frame.rootCursor = ⟨0, {}, []⟩ ∧
      frame.initialized = config.module.globals.size ∧
      frame.source.impl.params = #[] ∧ frame.source.impl.results = #[] ∧
      frame.source.scopes = [] ∧ frame.source.initializing = [] ∧ frame.interpretation.environment.scopes = [] ∧
      frame.interpretation.environment.channels = [] ∧
      freshAct state = .ok frame.interpretation.environment.act { state with nextAct := state.nextAct + 1 } ∧
      SourceFrameCompatible accepted frame ∧ AliasComplete frame.interpretation frame.source.aliases ∧
      RootFrontier frame.interpretation (state.nextAct + 1) ∧
      LocalRootCorrespondence frame.interpretation frame.source.ctx frame.typing.visible
        { state with nextAct := state.nextAct + 1 } ∧
      (∀ fuel, ContentRootCorrespondence frame.interpretation frame.source.ctx frame.typing.visible fuel config.layout
        { state with nextAct := state.nextAct + 1 }) ∧
      ∃ types declared, typeBlock frame.typingFuel frame.typing frame.source.impl.body frame.typingCounter =
        .ok (types, declared) := by
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
  obtain ⟨bodyTypes, typingAfter, bodyChecked⟩ :=
    validated_implementation_typing config.module original.impl implementation accepted.accepted implementationAt
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
  have typed : typeBlock frame.typingFuel frame.typing frame.source.impl.body frame.typingCounter =
      .ok (bodyTypes, typingAfter) := by
    simpa only [frame, typing, source, parametersEmpty, resultsEmpty, Array.size_empty,
      Array.toList_empty, List.map_nil, Array.isEmpty_empty, ite_true, List.range_zero] using bodyChecked
  exact ⟨frame, rfl, rfl, rfl, rfl, rfl, rfl, parametersEmpty, resultsEmpty, rfl, rfl, rfl, rfl, rfl,
    compatible, aliases, frontier, locals, contents, bodyTypes, typingAfter, typed⟩

theorem acceptedEmptyCallWorldFrame (config : EvalConfig) (accepted : AcceptedModule config) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (liveRoots : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat) (original : Context) (implementation : Impl)
    (originalAt : config.module.contexts[contextId]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (parameters : implementation.params = #[]) (results : implementation.results = #[])
    (world : AcceptedWorld config config.module.globals.size { state with nextAct := state.nextAct + 1 }
      ambient types liveRoots regions pending) :
    ∃ frame : ConstructionSourceFrame,
      AcceptedWorld config frame.initialized { state with nextAct := state.nextAct + 1 }
        ambient types liveRoots regions pending ∧
      AcceptedFrame config accepted frame { state with nextAct := state.nextAct + 1 } types ∧
      frame.phase = .implementation contextId ∧ frame.typing.visible = [] ∧
      frame.typingFuel = 4096 ∧ frame.typingCounter = 0 ∧ frame.rootCursor = ⟨0, {}, []⟩ ∧
      frame.initialized = config.module.globals.size ∧
      frame.source.impl.params = #[] ∧ frame.source.impl.results = #[] ∧
      frame.source.scopes = [] ∧ frame.interpretation.environment.scopes = [] ∧
      frame.interpretation.environment.channels = [] ∧
      freshAct state = .ok frame.interpretation.environment.act { state with nextAct := state.nextAct + 1 } ∧
      ∃ bodyTypes declared, typeBlock frame.typingFuel frame.typing frame.source.impl.body frame.typingCounter =
        .ok (bodyTypes, declared) := by
  obtain ⟨frame, phase, visible, fuel, counter, cursor, initialized, parametersEmpty, resultsEmpty,
      sourceScopes, initializing, scopes, channels, allocated, compatible, aliases, frontier, direct, contents,
      bodyTypes, declared, typed⟩ := acceptedEmptyCallFrame config accepted state contextId original implementation originalAt implementationAt parameters results
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
  exact ⟨frame, frameWorld, framed, phase, visible, fuel, counter, cursor, initialized, parametersEmpty, resultsEmpty,
    sourceScopes, scopes, channels, allocated, bodyTypes, declared, typed⟩

theorem acceptedCallStatementsFrame (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (contextId : Nat) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (phase : frame.phase = .implementation contextId)
    (parametersEmpty : frame.source.impl.params = #[])
    (scopes : frame.interpretation.environment.scopes = []) (initialized : frame.initialized = config.module.globals.size)
    (cursor : frame.rootCursor = ⟨0, {}, []⟩) :
    let next := entryStatementsFrame config frame state.nextScope
    let after := { state with nextScope := state.nextScope + 1 }
    freshScope state = .ok state.nextScope after ∧
    AcceptedWorld config next.initialized after ambient types live regions pending ∧
    AcceptedFrame config accepted next after types ∧
    SourcePosition accepted next (.statements frame.source.impl.body.stmts) := by
  let scope := frame.source.impl.body.scope
  let after := { state with nextScope := state.nextScope + 1 }
  let interpretation := frame.interpretation.enterScope scope state.nextScope
  let next := entryStatementsFrame config frame state.nextScope
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
    refine ⟨rfl, source.compatible.rootModule, ?_, rfl, ?_, source.compatible.globalCount, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, RootInterpretation.enterScope]
        using source.compatible.variables.trans source.compatible.sourceVariables.symm
    · simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, RootInterpretation.enterScope,
        scopes, List.map_cons, List.map_nil]
    · exact Nat.le_refl _
    · simpa only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using source.compatible.initialized
    · simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, parametersEmpty, Array.size_empty]
      exact Nat.le_refl _
    · simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, parametersEmpty, Array.size_empty]
      exact Nat.zero_le _
    · intro id member
      simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, parametersEmpty,
        Array.size_empty, List.range_zero, List.not_mem_nil] at member
    · intro id member
      simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, List.not_mem_nil] at member
    · intro current rest same
      simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, List.cons.injEq] at same
      change frame.source.impl.body.scope = current
      exact same.1
    · have origin := source.compatible.origin
      unfold SourceOrigin at origin ⊢
      rw [phase] at origin
      simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, RootInterpretation.enterScope, phase,
        initialized]
      obtain ⟨original, calls, found, implementation, environment, typing, remaining⟩ := origin
      exact ⟨original, calls, found, implementation, environment, True.intro, remaining⟩
  have framed : AcceptedFrame config accepted next after types := by
    refine ⟨compatible, frontier, ?_, ?_, aliases, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro entry member
      simp only [next, entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, scopes, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst entry
      exact Nat.lt_succ_self _
    · intro id member
      simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, List.not_mem_nil] at member
    · intro id member
      simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, parametersEmpty,
        Array.size_empty, List.range_zero, List.not_mem_nil] at member
    · intro id member
      simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, parametersEmpty,
        Array.size_empty, List.range_zero, List.not_mem_nil] at member
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
      change frame.initialized ≤ id at future
      rw [initialized] at future
      exact (Nat.not_lt_of_ge future bound).elim
    · intro id member
      simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, parametersEmpty,
        Array.size_empty, List.range_zero, List.not_mem_nil] at member
    · intro fuel id member
      simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, parametersEmpty,
        Array.size_empty, List.range_zero, List.not_mem_nil] at member
  have bodyPosition : SourcePosition accepted (implementationBodyFrame config frame) (.block frame.source.impl.body) :=
    .implementationBody frame contextId phase source.compatible
  have statementsPosition : SourcePosition accepted
      (blockStatementsFrame (implementationBodyFrame config frame) scope 4095) (.statements frame.source.impl.body.stmts) := by
    cases body : frame.source.impl.body with
    | mk scope' statements value =>
      rw [body] at bodyPosition
      simpa only [scope, body, Block.scope, Block.stmts, implementationBodyFrame] using
        bodyPosition.block_statements accepted (implementationBodyFrame config frame) scope' 4095 statements value rfl
  have position : SourcePosition accepted next (.statements frame.source.impl.body.stmts) := by
    exact .instantiate statementsPosition interpretation frame.initialized
  exact ⟨rfl, scopeWorld, framed, position⟩

theorem acceptedEmptyCallPushedStatements (config : EvalConfig) (accepted : AcceptedModule config)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat) (original : Context) (implementation : Impl)
    (originalAt : config.module.contexts[contextId]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (parametersEmpty : implementation.params = #[]) (resultsEmpty : implementation.results = #[])
    (world : AcceptedWorld config config.module.globals.size state ambient types live regions pending) :
    ∃ (frame : ConstructionSourceFrame) (activation : RuntimeActivation),
      let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let scopeState := { activated with nextScope := activated.nextScope + 1 }
      let after := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let next := entryStatementsFrame config frame activated.nextScope
      frame.initialized = config.module.globals.size ∧ frame.interpretation.environment = activation ∧ activation.act = state.nextAct ∧
      activation.scopes = [] ∧ activation.channels = [] ∧
      freshAct state = .ok activation.act { state with nextAct := state.nextAct + 1 } ∧
      freshScope activated = .ok activated.nextScope scopeState ∧
      AcceptedWorld config next.initialized after (.callChannels activation [] :: ambient) types live regions pending ∧
      AcceptedFrame config accepted next after types ∧
      SourcePosition accepted next (.statements frame.source.impl.body.stmts) ∧
      frame.phase = .implementation contextId ∧ frame.source.impl.params = #[] ∧ frame.source.impl.results = #[] ∧
      ∃ original, config.module.contexts[contextId]? = some original ∧
        config.module.impls[original.impl]? = some frame.source.impl ∧
        activation.implementation = original.impl ∧ activation.vars = frame.source.impl.vars := by
  let activation : RuntimeActivation := ⟨original.impl, state.nextAct, implementation.vars, [], []⟩
  let pushed := { state with activations := activation :: state.activations }
  have pushedWorld := acceptedWorld_pushEmptyActivation config config.module.globals.size state ambient types live regions pending
    activation world rfl rfl
  obtain ⟨frame, frameWorld, frameSource, phase, visible, fuel, counter, cursor, initialized, frameParameters, frameResults,
    sourceScopes, scopes, channels, allocated, bodyTypes, declared, typed⟩ :=
    acceptedEmptyCallWorldFrame config accepted pushed (.callChannels activation [] :: ambient) types live regions pending
      contextId original implementation originalAt implementationAt parametersEmpty resultsEmpty pushedWorld
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
  obtain ⟨fresh, scopeWorld, scopeSource, position⟩ := acceptedCallStatementsFrame config accepted frame contextId
    { pushed with nextAct := pushed.nextAct + 1 } (.callChannels activation [] :: ambient) types live regions pending
    frameWorld frameSource phase frameParameters scopes initialized cursor
  have scopeVisible : (entryStatementsFrame config frame state.nextScope).typing.visible = [] := by
    simp only [entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, frameParameters,
      Array.size_empty, List.range_zero]
  have actualSource := scopeSource.emptyVisible_activations scopeVisible
    (({ pushed with nextAct := pushed.nextAct + 1 }).activations.map (fun (current : RuntimeActivation) =>
      if current.act == activation.act then { current with scopes := (frame.source.impl.body.scope, state.nextScope) :: activation.scopes }
      else current))
  have actualWorld := acceptedWorld_resultScope config frame.initialized
    { pushed with nextAct := pushed.nextAct + 1 } (.callChannels activation [] :: ambient) types live regions pending
    activation frame.source.impl.body.scope frameWorld
  refine ⟨frame, activation, initialized, environment, rfl, rfl, rfl, ?_, fresh, actualWorld, actualSource, position, phase,
    frameParameters, frameResults, original, originalAt, ?_, rfl, ?_⟩
  · rfl
  · simpa only [sameImpl] using implementationAt
  · simp only [sameImpl, activation]

#print axioms acceptedEmptyCallPushedStatements
#print axioms acceptedCallStatementsFrame
#print axioms acceptedEmptyCallWorldFrame
#print axioms acceptedEmptyCallFrame
end Goose.Proofs.ConstructionAcceptedExecution
