import Goose.Proofs.ConstructionGhostGlobalEvents
import Goose.Proofs.ConstructionGhostChannelEntryEvents
import Goose.Proofs.ConstructionGhostChannelLengths

namespace Goose.Proofs.ConstructionGhostGlobalChannelEntryEvents
open Goose.Construct Goose.Proofs.ConstructionExecution
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSourceGlobal Goose.Proofs.ConstructionGhostGlobalStep Goose.Proofs.ConstructionGhostGlobalReplay
open Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostInvocationEventChunks
open Goose.Proofs.ConstructionGhostGlobalEvents Goose.Proofs.ConstructionGhostChannelEntryEvents
open Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostCallActivation
open Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostStatementEvents
open Goose.Proofs.ConstructionGhostResultScope Goose.Proofs.ConstructionGhostModuleInitializerEvents
open Goose.Proofs.ConstructionGhostMaterializedDeclarationEvents Goose.Proofs.ConstructionGhostDirectDeclarationEvents
open Goose.Proofs.ConstructionGhostNamedDeclarationEvents Goose.Proofs.ConstructionGhostChannelLengths

theorem runModule_globalAndChannelEntryEvents (fuel : Nat) (config : EvalConfig) (before : ExecutionState)
    (globalSupported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global),
      config.module.globals[global]? = some descriptor → ∀ environment,
      FuelSupport config (fuel + 3) (.value environment descriptor.init))
    (globalDirectSupported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global),
      config.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = true →
      ordinaryProducerCount? (fuel + 3) ⟨config.module, #[]⟩ descriptor.init = none →
      ∀ environment destination, SupportedOperation config (.builder environment destination descriptor.init))
    (context : Context) (implementation : Impl)
    (contextFound : config.module.contexts[config.module.entry]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (parametersEmpty : implementation.params = #[])
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (body : implementation.body = .mk scope statements tail)
    (entrySupported : ∀ act scopeInst channels sourceFuel localVar expression origin, .letS localVar expression origin ∈ statements →
      FuelSupport config sourceFuel (.value ⟨context.impl, act, implementation.vars, [(scope, scopeInst)], channels⟩ expression))
    (entryBuilderSupported : ∀ act scopeInst channels sourceFuel localVar expression origin descriptor,
      .letS localVar expression origin ∈ statements → implementation.vars[localVar]? = some descriptor → descriptor.ty.nonfixed = true →
      ∀ destination, FuelSupport config sourceFuel
        (.builder ⟨context.impl, act, implementation.vars, [(scope, scopeInst)], channels⟩ destination expression)) :
    ∃ globalOutcome globalVisits globalChunks,
      OperandReplay (globalInitializer (fuel + 3) config) 0 (List.range config.module.globals.size) [] before globalOutcome globalVisits ∧
      FixedSourceForest (fuel + 3) config globalVisits ∧ MaterializedSourceForest (fuel + 3) config globalVisits ∧
      DirectSourceForest (fuel + 3) config globalVisits ∧
      globalVisits.map Invocation.operand = (List.range config.module.globals.size).take globalVisits.length ∧
      (globalVisits.map Invocation.ordinal).Nodup ∧ ChunksAlign globalVisits globalChunks ∧
      (Goose.Proofs.Exit.stepState globalOutcome).construction.events = before.construction.events ++ globalChunks.flatten ∧
      runModule (fuel + 3) config before = moduleAfterGlobals (fuel + 3) config (discardGlobalValues globalOutcome) ∧
      ∀ initialized channels callReady, discardGlobalValues globalOutcome = .ok () initialized →
        channelsFor config.layout 0 implementation.results.toList 0 initialized = .ok channels callReady →
        runModule (fuel + 3) config before = entryCallResult
          (invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] channels 0 callReady) ∧
        ∀ callable argumentsReady refreshed activationReady,
          prepareCallableChannels ⟨0, 0, #[], [], []⟩ channels implementation 0 callReady = .ok callable argumentsReady →
          refreshCallableChannels callable 0 argumentsReady = .ok refreshed activationReady →
          activationReady.activations.length < Goose.Core.maxCallDepth →
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
            invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] channels 0 callReady =
              ((enterActivation (fuel + 2) config activation [] implementation.body 0 >>= fun carriers =>
                deliverCarriers (fuel + 2) config.layout channels carriers 0) activated) := by
  obtain ⟨globalOutcome, globalVisits, replay, forest, ordered, once, execution⟩ := runModule_globalReplay (fuel + 3) config before
  obtain ⟨globalChunks, aligned, finalEq, _, _⟩ := replay_eventChunks replay (globalInitializer_keepsEventPrefix (fuel + 3) config)
  have fixed := globalReplay_fuelSourceForest replay (fun global descriptor found _ environment => globalSupported global descriptor found environment)
  have materialized := globalReplay_materializedFuelSourceForest replay (fun global descriptor count found _ _ environment => globalSupported global descriptor found environment)
  refine ⟨globalOutcome, globalVisits, globalChunks, replay, fixed, materialized, globalReplay_directSourceForest replay globalDirectSupported,
    ordered, once, aligned, finalEq, execution, ?_⟩
  intro initialized channels callReady globals channelResult
  constructor
  · rw [execution, globals]
    simp only [moduleAfterGlobals, afterGlobals, bind, getImplementation, contextFound, implementationFound, pure, channelResult, entryCallResult]
    cases invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] channels 0 callReady <;> rfl
  · intro callable argumentsReady refreshed activationReady prepared refresh depth
    have arity : channels.length = implementation.results.size := by
      simpa using channelsFor_success_length config.layout 0 implementation.results.toList 0 initialized callReady channels channelResult
    have localSupported : ∀ sourceFuel localVar expression origin, .letS localVar expression origin ∈ statements →
        FuelSupport config sourceFuel
          (.value ⟨context.impl, activationReady.nextAct, implementation.vars, [(scope, activationReady.nextScope)], refreshed⟩ expression) := by
      intro sourceFuel localVar expression origin member
      exact entrySupported activationReady.nextAct activationReady.nextScope refreshed sourceFuel localVar expression origin member
    have localBuilders : ∀ sourceFuel localVar expression origin descriptor,
        .letS localVar expression origin ∈ statements → implementation.vars[localVar]? = some descriptor → descriptor.ty.nonfixed = true →
        ∀ destination, FuelSupport config sourceFuel
          (.builder ⟨context.impl, activationReady.nextAct, implementation.vars, [(scope, activationReady.nextScope)], refreshed⟩ destination expression) := by
      intro sourceFuel localVar expression origin descriptor member found nonfixed destination
      exact entryBuilderSupported activationReady.nextAct activationReady.nextScope refreshed sourceFuel localVar expression origin descriptor
        member found nonfixed destination
    obtain ⟨outcome, visits, chunks, statementReplay, statementOrdered, statementOnce, statementAligned, statementFinal,
      fixedSources, materializedSources, directSources, namedSources, callExecution, enterExecution⟩ :=
      channelEntry_initializerEvents fuel config callReady argumentsReady activationReady config.module.entry context implementation
        channels callable refreshed 0 contextFound implementationFound parametersEmpty arity prepared refresh depth
        scope statements tail body localSupported localBuilders
    exact ⟨outcome, visits, chunks, statementReplay, statementOrdered, statementOnce, statementAligned, statementFinal,
      fixedSources, materializedSources, directSources, namedSources, callExecution⟩

#print axioms runModule_globalAndChannelEntryEvents
end Goose.Proofs.ConstructionGhostGlobalChannelEntryEvents
