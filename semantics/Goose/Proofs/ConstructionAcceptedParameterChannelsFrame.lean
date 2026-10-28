import Goose.Proofs.ConstructionAcceptedParameterFrame
import Goose.Proofs.ConstructionAcceptedRegisterCall
import Goose.Proofs.ConstructionAcceptedParameterFrameList

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

def twoParameterBodyFrame (frame : ConstructionSourceFrame) (scopeInstance : Nat) : ConstructionSourceFrame :=
  let advanced := advanceLocalFrame (advanceLocalFrame (parameterScopeFrame frame scopeInstance) 0) 1
  { advanced with typing := { advanced.typing with visible := [0, 1] }, typingFuel := 4095 }

def parameterListBodyFrame (frame : ConstructionSourceFrame) (scopeInstance count : Nat) : ConstructionSourceFrame :=
  let advanced := advanceParameterFrames (parameterScopeFrame frame scopeInstance) 0 count
  { advanced with typing := { advanced.typing with visible := List.range count }, typingFuel := 4095 }

theorem acceptedParameterCallFrameForChannels (config : EvalConfig) (accepted : AcceptedModule config) (state : ExecutionState) (contextId : Nat) (original : Context) (implementation : Impl)
    (channels : List Channel) (originalAt : config.module.contexts[contextId]? = some original)
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
      frame.interpretation.environment.channels = channels ∧
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
  let environment : RuntimeActivation := ⟨original.impl, state.nextAct, implementation.vars, [], channels⟩
  let interpretation := EntryInterpretation environment config.module.globals.size
  let typing : TypingEnv := {
    module := config.module
    implementation := some implementation
    variables := implementation.vars
    visible := []
    scope := implementation.body.scope
    loops := 0
    use := if implementation.results.isEmpty then .ordinary else .result
    request := .value
    resultRequests := implementation.results.toList.map (·.request)
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
  have aligned : implementation.params.size = 1 → ∀ scopeInstance,
      { advanceLocalFrame (parameterScopeFrame frame scopeInstance) 0 with typingFuel := 4095 } =
        entryStatementsFrame config frame scopeInstance := by
    intro parameters scopeInstance
    simp [frame, typing, source, parameterScopeFrame, advanceLocalFrame, entryStatementsFrame,
      blockStatementsFrame, implementationBodyFrame, parameters, List.range]
    rfl
  have alignedTwo : implementation.params.size = 2 → ∀ scopeInstance,
      twoParameterBodyFrame frame scopeInstance = entryStatementsFrame config frame scopeInstance := by
    intro parameters scopeInstance
    simp [twoParameterBodyFrame, frame, typing, source, parameterScopeFrame, advanceLocalFrame,
      entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, parameters, List.range]
    rfl
  have alignedList : ∀ scopeInstance, parameterListBodyFrame frame scopeInstance implementation.params.size = entryStatementsFrame config frame scopeInstance := by
    intro scopeInstance
    simp [parameterListBodyFrame, advanceParameterFrames_eq, frame, typing, source, parameterScopeFrame,
      entryStatementsFrame, blockStatementsFrame, implementationBodyFrame]
  exact ⟨frame, ⟨aligned, alignedTwo⟩, alignedList, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    compatible, aliases, frontier, locals, contents⟩


#print axioms acceptedParameterCallFrameForChannels
end Goose.Proofs.ConstructionAcceptedExecution
