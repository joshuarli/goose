import Goose.Proofs.ConstructionGhostChannelEntryEvents
import Goose.Proofs.ConstructionGhostSourceGlobal

namespace Goose.Proofs.ConstructionGhostChannelEntryEventsWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostCallActivation
open Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostStatementEvents
open Goose.Proofs.ConstructionGhostInvocationEventChunks Goose.Proofs.ConstructionGhostNamedDeclarationEvents
open Goose.Proofs.ConstructionGhostChannelEntryEvents Goose.Proofs.ConstructionGhostSourceGlobal

private def context : Context := ⟨0, "entry", [], [], []⟩
private def expression : Expr := .bytes (.varr (.int .u8)) [65, 66] 0
private def descriptor : LocalVar := ⟨"named", .varr (.int .u8), .immutable, 0, 0⟩
private def result : ResultDescriptor := ⟨.varr (.int .u8), .value, some 0⟩
private def statement : Stmt := .letS 0 expression 0
private def implementation : Impl := ⟨"entry", #[], #[result], #[descriptor], .mk 0 [statement] (some (.resultLocal 0 0)), .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state
private def callReady : ExecutionState := stepState (channelsFor config.layout 0 implementation.results.toList 0 .initial)
private def argumentsReady : ExecutionState := stepState (prepareCallableChannels environment [.construct 0] implementation 0 callReady)
private def activationReady : ExecutionState := stepState (refreshCallableChannels [.construct 0] 0 argumentsReady)

theorem namedModule_entryEvents : ∃ outcome visits chunks final,
    let activation : RuntimeActivation := ⟨0, activationReady.nextAct, implementation.vars, [], [.construct 0]⟩
    let activated := { activationReady with nextAct := activationReady.nextAct + 1, activations := activation :: activationReady.activations }
    let ready := Goose.Proofs.ConstructionGhostResultScope.resultScopeStart activation 0 activated
    let scopedEnvironment := { activation with scopes := (0, activated.nextScope) :: activation.scopes }
    StatementReplay config scopedEnvironment 37 0 [statement] ready outcome visits ∧
    visits.map StatementInvocation.statement = [statement].take visits.length ∧
    (visits.map StatementInvocation.ordinal).Nodup ∧ ChunksAlign (visits.map statementInvocation) chunks ∧
    NamedVisitSourceEvents config scopedEnvironment visits ∧
    runModule 40 config .initial = entryCallResult (invokeCall 40 config environment 0 [] [.construct 0] 0 callReady) ∧
    invokeCall 40 config environment 0 [] [.construct 0] 0 callReady =
      ((enterActivation 39 config activation [] implementation.body 0 >>= fun carriers =>
        deliverCarriers 39 config.layout [.construct 0] carriers 0) activated) ∧
    runModule 40 config .initial = .ok () final ∧ final.construction.events ≠ [] := by
  have channelResult : channelsFor config.layout 0 implementation.results.toList 0 .initial = .ok [.construct 0] callReady := by
    simp only [callReady, stepState, config, context, implementation, result, descriptor, expression, statement]
    cbv
  have prepared : prepareCallableChannels environment [.construct 0] implementation 0 callReady = .ok [.construct 0] argumentsReady := by
    simp only [argumentsReady, callReady, stepState, config, context, implementation, result, descriptor, expression, statement, environment]
    cbv
  have refresh : refreshCallableChannels [.construct 0] 0 argumentsReady = .ok [.construct 0] activationReady := by
    simp only [activationReady, argumentsReady, callReady, stepState, config, context, implementation, result, descriptor, expression, statement, environment]
    cbv
  have depth : activationReady.activations.length < Goose.Core.maxCallDepth := by
    simp only [activationReady, argumentsReady, callReady, stepState, config, context, implementation, result, descriptor, expression, statement, environment]
    cbv
  have supported : ∀ sourceFuel id expr statementOrigin, .letS id expr statementOrigin ∈ [statement] →
      FuelSupport config sourceFuel (.value ⟨0, activationReady.nextAct, implementation.vars, [(0, activationReady.nextScope)], [.construct 0]⟩ expr) := by
    intro sourceFuel id expr statementOrigin member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    have same : Stmt.letS id expr statementOrigin = Stmt.letS 0 expression 0 := member
    cases same
    exact .legacy sourceFuel (.valueBytes _ (.varr (.int .u8)) [65, 66] 0)
  have builders : ∀ sourceFuel id expr statementOrigin localDescriptor,
      .letS id expr statementOrigin ∈ [statement] → implementation.vars[id]? = some localDescriptor → localDescriptor.ty.nonfixed = true → ∀ destination,
      FuelSupport config sourceFuel (.builder ⟨0, activationReady.nextAct, implementation.vars, [(0, activationReady.nextScope)], [.construct 0]⟩ destination expr) := by
    intro sourceFuel id expr statementOrigin localDescriptor member found nonfixed destination
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    have same : Stmt.letS id expr statementOrigin = Stmt.letS 0 expression 0 := member
    cases same
    exact .legacy sourceFuel (.builderBytes _ destination (.varr (.int .u8)) [65, 66] 0)
  obtain ⟨outcome, visits, chunks, replay, ordered, once, aligned, finalEq, fixed, materialized, direct, named, callExecution, enterExecution⟩ :=
    channelEntry_initializerEvents 37 config callReady argumentsReady activationReady 0 context implementation [.construct 0] [.construct 0] [.construct 0] 0
      rfl rfl rfl rfl prepared refresh depth 0 [statement] (some (.resultLocal 0 0)) rfl supported builders
  have lookup : getImplementation config 0 .initial = .ok (0, implementation) .initial := by
    simp [getImplementation, config, context, implementation, bind, pure]
  have moduleExecution : runModule 40 config .initial = entryCallResult
      (invokeCall 40 config environment 0 [] [.construct 0] 0 callReady) := by
    have noGlobals : config.module.globals.size = 0 := rfl
    have entry : config.module.entry = 0 := rfl
    simp only [runModule, noGlobals, List.range_zero, initGlobals, bind, pure, entry, lookup, channelResult, entryCallResult]
    simp only [environment]
    cases invokeCall 40 config ⟨0, 0, #[], [], []⟩ 0 [] [.construct 0] 0 callReady <;> rfl
  refine ⟨outcome, visits, chunks, stepState (runModule 40 config .initial), replay, ordered, once, aligned, named,
    moduleExecution, callExecution, ?_, ?_⟩
  · simp only [stepState, config, context, implementation, result, descriptor, expression, statement]
    cbv
  · intro empty
    simp only [stepState, config, context, implementation, result, descriptor, expression, statement] at empty
    cbv at empty
    cases empty

#print axioms namedModule_entryEvents
end Goose.Proofs.ConstructionGhostChannelEntryEventsWitness
