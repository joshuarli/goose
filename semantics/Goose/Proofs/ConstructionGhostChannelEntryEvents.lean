import Goose.Proofs.ConstructionGhostEntryInitializerEvents
import Goose.Proofs.ConstructionGhostNamedDeclarationEvents

namespace Goose.Proofs.ConstructionGhostChannelEntryEvents
open Goose.Construct Goose.Proofs.ConstructionExecution
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostCallActivation
open Goose.Proofs.ConstructionGhostResultScope Goose.Proofs.ConstructionGhostStatements
open Goose.Proofs.ConstructionGhostStatementEvents Goose.Proofs.ConstructionGhostInvocationEventChunks
open Goose.Proofs.ConstructionGhostActivationEvents Goose.Proofs.ConstructionGhostModuleInitializerEvents
open Goose.Proofs.ConstructionGhostMaterializedDeclarationEvents Goose.Proofs.ConstructionGhostDirectDeclarationEvents
open Goose.Proofs.ConstructionGhostNamedDeclarationEvents

theorem channelEntry_initializerEvents (fuel : Nat) (config : EvalConfig) (before argumentsReady activationReady : ExecutionState)
    (contextId : Goose.Core.ContextId) (context : Context) (implementation : Impl) (channels callableChannels refreshed : List Channel)
    (origin : Goose.Core.OriginId)
    (contextFound : config.module.contexts[contextId]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (parametersEmpty : implementation.params = #[]) (arity : channels.length = implementation.results.size)
    (prepared : prepareCallableChannels ⟨0, 0, #[], [], []⟩ channels implementation origin before = .ok callableChannels argumentsReady)
    (refresh : refreshCallableChannels callableChannels origin argumentsReady = .ok refreshed activationReady)
    (depth : activationReady.activations.length < Goose.Core.maxCallDepth)
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (body : implementation.body = .mk scope statements tail)
    (supported : ∀ sourceFuel localVar expression statementOrigin, .letS localVar expression statementOrigin ∈ statements →
      FuelSupport config sourceFuel
        (.value ⟨context.impl, activationReady.nextAct, implementation.vars, [(scope, activationReady.nextScope)], refreshed⟩ expression))
    (builderSupported : ∀ sourceFuel localVar expression statementOrigin descriptor,
      .letS localVar expression statementOrigin ∈ statements → implementation.vars[localVar]? = some descriptor → descriptor.ty.nonfixed = true →
      ∀ destination, FuelSupport config sourceFuel
        (.builder ⟨context.impl, activationReady.nextAct, implementation.vars, [(scope, activationReady.nextScope)], refreshed⟩ destination expression)) :
    let activation : RuntimeActivation := ⟨context.impl, activationReady.nextAct, implementation.vars, [], refreshed⟩
    let activated := { activationReady with nextAct := activationReady.nextAct + 1, activations := activation :: activationReady.activations }
    let ready := resultScopeStart activation scope activated
    let scopedEnvironment := { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
    ∃ outcome visits chunks,
      StatementReplay config scopedEnvironment fuel 0 statements ready outcome visits ∧
      visits.map StatementInvocation.statement = statements.take visits.length ∧
      (visits.map StatementInvocation.ordinal).Nodup ∧ ChunksAlign (visits.map statementInvocation) chunks ∧
      (Goose.Proofs.Exit.stepState outcome).construction.events = ready.construction.events ++ chunks.flatten ∧
      FixedVisitSourceEvents config scopedEnvironment visits ∧ MaterializedVisitSourceEvents config scopedEnvironment visits ∧
      DirectVisitSourceEvents config scopedEnvironment visits ∧ NamedVisitSourceEvents config scopedEnvironment visits ∧
      invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ contextId [] channels origin before =
        ((enterActivation (fuel + 2) config activation [] implementation.body origin >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout channels carriers origin) activated) ∧
      enterActivation (fuel + 2) config activation [] implementation.body origin activated =
        finishActivation config.layout activation (implementation.results.toList.map (·.ty)) origin
          (execActivationBody (fuel + 1) config activation [] implementation.body) activated := by
  dsimp only
  let activation : RuntimeActivation := ⟨context.impl, activationReady.nextAct, implementation.vars, [], refreshed⟩
  let activated := { activationReady with nextAct := activationReady.nextAct + 1, activations := activation :: activationReady.activations }
  let ready := resultScopeStart activation scope activated
  have bound : bindAll activation.act activated.nextScope [] ready = .ok () ready := by simp [bindAll, bind, pure]
  have localSupported : ∀ sourceFuel localVar expression statementOrigin, .letS localVar expression statementOrigin ∈ statements →
      FuelSupport config sourceFuel (.value { activation with scopes := (scope, activated.nextScope) :: activation.scopes } expression) := by
    intro sourceFuel localVar expression statementOrigin member
    exact supported sourceFuel localVar expression statementOrigin member
  have localBuilders : ∀ sourceFuel localVar expression statementOrigin descriptor,
      .letS localVar expression statementOrigin ∈ statements →
      ({ activation with scopes := (scope, activated.nextScope) :: activation.scopes } : RuntimeActivation).vars[localVar]? = some descriptor →
      descriptor.ty.nonfixed = true → ∀ destination,
      FuelSupport config sourceFuel (.builder { activation with scopes := (scope, activated.nextScope) :: activation.scopes } destination expression) := by
    intro sourceFuel localVar expression statementOrigin descriptor member found nonfixed destination
    exact builderSupported sourceFuel localVar expression statementOrigin descriptor member found nonfixed destination
  obtain ⟨outcome, visits, chunks, replay, ordered, once, aligned, finalEq, execution, fixed⟩ :=
    activationBody_fixedSourceEvents fuel config activation [] scope statements tail activated ready bound localSupported
  refine ⟨outcome, visits, chunks, replay, ordered, once, aligned, finalEq, fixed,
    statementReplay_materializedSourceEvents replay localSupported, ?_, ?_, ?_, ?_⟩
  · apply statementReplay_directSourceEvents_guarded replay
    intro sourceFuel localVar expression statementOrigin descriptor member found nonfixed direct destination
    exact localBuilders sourceFuel localVar expression statementOrigin descriptor member found nonfixed destination
  · exact statementReplay_namedSourceEvents_guarded replay localBuilders
  · have lookup : getImplementation config contextId before = .ok (context.impl, implementation) before := by
      simp [getImplementation, contextFound, implementationFound, bind, pure]
    obtain ⟨argumentsOutcome, argumentsVisits, argumentsReplay, argumentsOrdered, argumentsOnce, callExecution⟩ :=
      invokeCall_argumentReplay (fuel + 2) config ⟨0, 0, #[], [], []⟩ contextId [] channels origin before before argumentsReady
        context.impl implementation callableChannels lookup arity prepared
    have argumentsResult : evalArguments (fuel + 2) config ⟨0, 0, #[], [], []⟩ implementation.vars implementation.params.toList [] argumentsReady = .ok [] argumentsReady := by
      simp [parametersEmpty, evalArguments, pure]
    have actual := argumentsReplay.sound
    rw [argumentsResult] at actual
    subst argumentsOutcome
    rw [callExecution]
    simpa [callArgumentsContinuation, parametersEmpty] using
      (callAfterArguments_activation (fuel + 2) config context.impl implementation channels callableChannels refreshed origin []
        argumentsReady activationReady refresh depth)
  · simp only [enterActivation, implementationFound]

#print axioms channelEntry_initializerEvents
end Goose.Proofs.ConstructionGhostChannelEntryEvents
