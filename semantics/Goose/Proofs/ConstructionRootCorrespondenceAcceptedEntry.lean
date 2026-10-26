import Goose.Proofs.ConstructionAcceptedSource

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem acceptedEntryFrame (config : EvalConfig) (accepted : AcceptedModule config) (state : ExecutionState) :
    ∃ frame : ConstructionSourceFrame,
      frame.phase = .implementation config.module.entry ∧ frame.typing.visible = [] ∧
      frame.typingFuel = 4096 ∧ frame.typingCounter = 0 ∧ frame.rootCursor = ⟨0, {}, []⟩ ∧
      frame.initialized = config.module.globals.size ∧
      frame.source.impl.params = #[] ∧ frame.source.impl.results = #[] ∧
      frame.source.scopes = [] ∧ frame.interpretation.environment.scopes = [] ∧
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
  obtain ⟨original, implementation, originalAt, implementationAt, parametersEmpty, resultsEmpty⟩ :=
    validated_entry config.module accepted.accepted
  have member : (original, config.module.entry) ∈ config.module.contexts.toList.zipIdx := by
    apply List.mem_of_getElem? (i := config.module.entry)
    simp only [List.getElem?_zipIdx, Array.getElem?_toList, originalAt, Option.map_some, Nat.zero_add]
  obtain ⟨calls, contextFacts, _⟩ := (Classical.choose_spec accepted.roots).2.1
    (original, config.module.entry) member
  obtain ⟨escaping, names, contextFactsAt⟩ := contextFacts
  obtain ⟨bodyImplementation, bodyContext, targetEscapes, roots, rootAfter,
      bodyImplementationAt, closed, targetsChecked, rootsChecked⟩ :=
    contextRootFactsAt_bodyRoots config.module original accepted.aliases[config.module.entry]! calls
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
    aliases := accepted.aliases[config.module.entry]!
    calleeNames := names }
  let frame : ConstructionSourceFrame := {
    phase := .implementation config.module.entry
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
      refine ⟨original, calls, originalAt, implementationAt, rfl, rfl, closed, rfl, contextFactsAt,
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
  exact ⟨frame, rfl, rfl, rfl, rfl, rfl, rfl, parametersEmpty, resultsEmpty, rfl, rfl, rfl, rfl,
    compatible, aliases, frontier, locals, contents, bodyTypes, typingAfter, typed⟩

end Goose.Proofs.ConstructionAcceptedExecution
