import Goose.Proofs.ConstructionAcceptedSource

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private theorem accepted_parameterCount (module : Module) (id : Nat) (implementation : Impl)
    (accepted : validate module = .ok ()) (present : module.impls[id]? = some implementation) :
    implementation.params.size ≤ implementation.vars.size := by
  by_cases bounded : implementation.params.size ≤ implementation.vars.size
  · exact bounded
  ·
    have bound : implementation.vars.size < implementation.params.size := Nat.lt_of_not_ge bounded
    let parameter := implementation.params[implementation.vars.size]'bound
    have parameterAt : implementation.params[implementation.vars.size]? = some parameter := by simp [parameter]
    have dense := validated_parameter_variable module id implementation implementation.vars.size parameter
      accepted present parameterAt
    obtain ⟨descriptor, descriptorAt⟩ := validated_parameter_descriptor module id implementation implementation.vars.size
      parameter accepted present parameterAt
    rw [dense] at descriptorAt
    exact (Nat.lt_irrefl _ (Array.getElem?_eq_some_iff.mp descriptorAt).1).elim

theorem acceptedCalleeSourceFrame (config : EvalConfig) (accepted : AcceptedModule config)
    (caller : ConstructionSourceFrame) (state : ExecutionState) (target : Nat)
    (original : Context) (implementation : Impl) (argumentRoots : List (List RootRef)) (channels : List Channel)
    (callerCompatible : SourceFrameCompatible accepted caller)
    (callerFrontier : RootFrontier caller.interpretation state.nextAct)
    (contextAt : config.module.contexts[target]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation) :
    ∃ frame : ConstructionSourceFrame,
      frame.phase = .implementation target ∧ frame.source.impl = implementation ∧
      frame.source.aliases = accepted.aliases[target]! ∧
      frame.interpretation = CallInterpretation caller.interpretation
        ⟨original.impl, state.nextAct, implementation.vars, [], channels⟩ argumentRoots ∧
      frame.initialized = caller.initialized ∧ implementationBodyFrame config frame = frame ∧
      SourceFrameCompatible accepted frame ∧
      freshAct state = .ok frame.interpretation.environment.act { state with nextAct := state.nextAct + 1 } ∧
      RootFrontier frame.interpretation (state.nextAct + 1) := by
  have member : (original, target) ∈ config.module.contexts.toList.zipIdx := by
    apply List.mem_of_getElem? (i := target)
    simp only [List.getElem?_zipIdx, Array.getElem?_toList, contextAt, Option.map_some, Nat.zero_add]
  obtain ⟨calls, contextFacts, callsCovered⟩ := (Classical.choose_spec accepted.roots).2.1 (original, target) member
  obtain ⟨escaping, names, contextFactsAt⟩ := contextFacts
  obtain ⟨bodyImplementation, bodyContext, targetEscapes, roots, rootAfter,
      bodyImplementationAt, closed, targetsChecked, rootsChecked, _bodyCallsIncluded⟩ :=
    contextRootFactsAt_bodyRoots config.module original accepted.aliases[target]! calls escaping names contextFactsAt
  have same : bodyImplementation = implementation := by
    simpa only [implementationAt, Option.some.injEq] using bodyImplementationAt.symm
  subst bodyImplementation
  let environment : RuntimeActivation := ⟨original.impl, state.nextAct, implementation.vars, [], channels⟩
  let interpretation := CallInterpretation caller.interpretation environment argumentRoots
  let source : PEnv := {
    mod := config.module
    impl := implementation
    ctx := bodyContext
    scopes := []
    escaping := escaping
    targetEscapes := targetEscapes
    aliases := accepted.aliases[target]!
    calleeNames := names }
  let seed := { caller with phase := .implementation target, source := source, interpretation := interpretation }
  let frame := implementationBodyFrame config seed
  have compatible : SourceFrameCompatible accepted frame := {
    module := rfl
    rootModule := rfl
    variables := rfl
    sourceVariables := rfl
    scopes := rfl
    globalCount := callerCompatible.globalCount
    globals := Nat.le_refl _
    initialized := callerCompatible.initialized
    declarations := Nat.le_refl _
    typingBound := accepted_parameterCount config.module original.impl implementation accepted.accepted implementationAt
    visible := by intro id present; exact List.mem_range.mp present
    initializing := by intro id absent; cases absent
    currentScope := by intro scope rest absent; cases absent
    origin := by
      refine ⟨original, calls, contextAt, implementationAt, rfl, rfl, closed, rfl,
        contextFactsAt, callsCovered, targetsChecked, roots, rootAfter, ?_⟩
      simpa only [frame, seed, source, implementationBodyFrame] using rootsChecked }
  refine ⟨frame, rfl, rfl, rfl, rfl, rfl, rfl, compatible, ?_, ?_⟩
  · exact (freshAct_callFrontier caller.interpretation environment argumentRoots state callerFrontier).1
  · exact call_rootFrontier caller.interpretation environment argumentRoots _ callerFrontier (Nat.lt_succ_self _)

end Goose.Proofs.ConstructionAcceptedExecution
