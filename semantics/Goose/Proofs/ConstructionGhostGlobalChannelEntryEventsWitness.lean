import Goose.Proofs.ConstructionGhostGlobalChannelEntryEvents

namespace Goose.Proofs.ConstructionGhostGlobalChannelEntryEventsWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostGlobalStep Goose.Proofs.ConstructionGhostGlobalReplay
open Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostInvocationEventChunks
open Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostCallActivation
open Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostStatementEvents
open Goose.Proofs.ConstructionGhostNamedDeclarationEvents Goose.Proofs.ConstructionGhostGlobalChannelEntryEvents

private def context : Context := ⟨0, "entry", [], [], []⟩
private def expression : Expr := .bytes (.varr (.int .u8)) [65, 66] 0
private def descriptor : LocalVar := ⟨"named", .varr (.int .u8), .immutable, 0, 0⟩
private def result : ResultDescriptor := ⟨.varr (.int .u8), .value, some 0⟩
private def statement : Stmt := .letS 0 expression 0
private def implementation : Impl := ⟨"entry", #[], #[result], #[descriptor], .mk 0 [statement] (some (.resultLocal 0 0)), .unknown⟩
private def global : Global := ⟨"global", .varr (.int .u8), .immutable, expression, 0⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[global], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state
private def initialized : ExecutionState := stepState (globalInitializer 40 config 0 .initial)
private def callReady : ExecutionState := stepState (channelsFor config.layout 0 implementation.results.toList 0 initialized)
private def argumentsReady : ExecutionState := stepState (prepareCallableChannels environment [.construct 1] implementation 0 callReady)
private def activationReady : ExecutionState := stepState (refreshCallableChannels [.construct 1] 0 argumentsReady)

private theorem globalDescriptor (id : Goose.Core.GlobalId) (actual : Global) (found : config.module.globals[id]? = some actual) : actual = global := by
  cases id with
  | zero => simpa [config] using found.symm
  | succ n => simp [config] at found

private theorem globalSupported : ∀ (id : Goose.Core.GlobalId) (actual : Global),
    config.module.globals[id]? = some actual → ∀ environment, FuelSupport config 40 (.value environment actual.init) := by
  intro id actual found environment
  have same := globalDescriptor id actual found
  subst actual
  exact .legacy 40 (.valueBytes environment (.varr (.int .u8)) [65, 66] 0)

private theorem globalDirectSupported : ∀ (id : Goose.Core.GlobalId) (actual : Global),
    config.module.globals[id]? = some actual → actual.ty.nonfixed = true →
    ordinaryProducerCount? 40 ⟨config.module, #[]⟩ actual.init = none → ∀ environment destination,
    SupportedOperation config (.builder environment destination actual.init) := by
  intro id actual found nonfixed direct environment destination
  have same := globalDescriptor id actual found
  subst actual
  exact .builderBytes environment destination (.varr (.int .u8)) [65, 66] 0

private theorem supported : ∀ act scopeInst channels sourceFuel id expr statementOrigin,
    .letS id expr statementOrigin ∈ [statement] → FuelSupport config sourceFuel
      (.value ⟨0, act, implementation.vars, [(0, scopeInst)], channels⟩ expr) := by
  intro act scopeInst channels sourceFuel id expr statementOrigin member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  have same : Stmt.letS id expr statementOrigin = Stmt.letS 0 expression 0 := member
  cases same
  exact .legacy sourceFuel (.valueBytes _ (.varr (.int .u8)) [65, 66] 0)

private theorem builders : ∀ act scopeInst channels sourceFuel id expr statementOrigin localDescriptor,
    .letS id expr statementOrigin ∈ [statement] → implementation.vars[id]? = some localDescriptor →
    localDescriptor.ty.nonfixed = true → ∀ destination, FuelSupport config sourceFuel
      (.builder ⟨0, act, implementation.vars, [(0, scopeInst)], channels⟩ destination expr) := by
  intro act scopeInst channels sourceFuel id expr statementOrigin localDescriptor member found nonfixed destination
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  have same : Stmt.letS id expr statementOrigin = Stmt.letS 0 expression 0 := member
  cases same
  exact .legacy sourceFuel (.builderBytes _ destination (.varr (.int .u8)) [65, 66] 0)

theorem globalThenNamedEntry : ∃ globalOutcome globalVisits globalChunks entryOutcome entryVisits entryChunks final,
    OperandReplay (globalInitializer 40 config) 0 [0] [] .initial globalOutcome globalVisits ∧
    ChunksAlign globalVisits globalChunks ∧ globalChunks.flatten ≠ [] ∧ discardGlobalValues globalOutcome = .ok () initialized ∧
    let activation : RuntimeActivation := ⟨0, activationReady.nextAct, implementation.vars, [], [.construct 1]⟩
    let activated := { activationReady with nextAct := activationReady.nextAct + 1, activations := activation :: activationReady.activations }
    let ready := Goose.Proofs.ConstructionGhostResultScope.resultScopeStart activation 0 activated
    let scopedEnvironment := { activation with scopes := (0, activated.nextScope) :: activation.scopes }
    StatementReplay config scopedEnvironment 37 0 [statement] ready entryOutcome entryVisits ∧
    (entryVisits.map StatementInvocation.ordinal).Nodup ∧ ChunksAlign (entryVisits.map statementInvocation) entryChunks ∧
    NamedVisitSourceEvents config scopedEnvironment entryVisits ∧ entryChunks.flatten ≠ [] ∧
    runModule 40 config .initial = .ok () final ∧ final.construction.events ≠ [] := by
  obtain ⟨globalOutcome, globalVisits, globalChunks, replay, globalFixed, globalMaterialized, globalDirect,
    ordered, once, aligned, finalEq, moduleExecution, entry⟩ :=
    runModule_globalAndChannelEntryEvents 37 config .initial globalSupported globalDirectSupported context implementation rfl rfl rfl
      0 [statement] (some (.resultLocal 0 0)) rfl supported builders
  have globalActual : globalInitializer 40 config 0 .initial = .ok () initialized := by
    simp only [initialized, stepState, globalInitializer, config, context, implementation, result, descriptor, global, expression, statement]
    cbv
  let visit : Invocation Goose.Core.GlobalId Unit := ⟨0, 0, .initial, .ok () initialized⟩
  have knownReplay : OperandReplay (globalInitializer 40 config) 0 [0] [] .initial (.ok [()] initialized) [visit] :=
    .next globalActual (.done 1 [()] initialized)
  have globalEq : globalOutcome = .ok [()] initialized := by
    have actualReplay : OperandReplay (globalInitializer 40 config) 0 [0] [] .initial globalOutcome globalVisits := by
      simpa [config] using replay
    exact actualReplay.execute.symm.trans knownReplay.execute
  have globalsDone : discardGlobalValues globalOutcome = .ok () initialized := by rw [globalEq]; rfl
  have channelResult : channelsFor config.layout 0 implementation.results.toList 0 initialized = .ok [.construct 1] callReady := by
    simp only [callReady, initialized, stepState, globalInitializer, config, context, implementation, result, descriptor, global, expression, statement]
    cbv
  have prepared : prepareCallableChannels environment [.construct 1] implementation 0 callReady = .ok [.construct 1] argumentsReady := by
    simp only [argumentsReady, callReady, initialized, stepState, globalInitializer, config, context, implementation, result, descriptor, global, expression, statement, environment]
    cbv
  have refresh : refreshCallableChannels [.construct 1] 0 argumentsReady = .ok [.construct 1] activationReady := by
    simp only [activationReady, argumentsReady, callReady, initialized, stepState, globalInitializer, config, context, implementation, result, descriptor, global, expression, statement, environment]
    cbv
  have depth : activationReady.activations.length < Goose.Core.maxCallDepth := by
    simp only [activationReady, argumentsReady, callReady, initialized, stepState, globalInitializer, config, context, implementation, result, descriptor, global, expression, statement, environment]
    cbv
  obtain ⟨moduleCall, reached⟩ := entry initialized [.construct 1] callReady globalsDone channelResult
  obtain ⟨entryOutcome, entryVisits, entryChunks, entryReplay, entryOrdered, entryOnce, entryAligned, entryFinal,
    fixed, materialized, direct, named, callExecution⟩ := reached [.construct 1] argumentsReady [.construct 1] activationReady prepared refresh depth
  refine ⟨globalOutcome, globalVisits, globalChunks, entryOutcome, entryVisits, entryChunks, stepState (runModule 40 config .initial),
    ?_, aligned, ?_, globalsDone, entryReplay, entryOnce, entryAligned, named, ?_, ?_, ?_⟩
  · simpa [config] using replay
  · have prefixEq : (Goose.Proofs.Exit.stepState globalOutcome).construction.events = globalChunks.flatten := by
      simpa [ExecutionState.initial, ConstructionState.initial] using finalEq
    rw [← prefixEq, globalEq]
    intro empty
    simp only [initialized, stepState, globalInitializer, config, context, implementation, result, descriptor, global, expression, statement] at empty
    cbv at empty
    cases empty
  · intro empty
    have finalEvents := entryFinal
    simp only [empty, List.flatten_nil, List.append_nil] at finalEvents
    rw [← entryReplay.sound] at finalEvents
    simp only [activationReady, argumentsReady, callReady, initialized, stepState, globalInitializer, config, context, implementation,
      result, descriptor, global, expression, statement, environment, Goose.Proofs.ConstructionGhostResultScope.resultScopeStart] at finalEvents
    cbv at finalEvents
    all_goals try (unfold evalValue at finalEvents; cbv at finalEvents)
    all_goals cases finalEvents
  · simp only [stepState, config, context, implementation, result, descriptor, global, expression, statement]
    cbv
  · intro empty
    simp only [stepState, config, context, implementation, result, descriptor, global, expression, statement] at empty
    cbv at empty
    cases empty

#print axioms globalThenNamedEntry
end Goose.Proofs.ConstructionGhostGlobalChannelEntryEventsWitness
