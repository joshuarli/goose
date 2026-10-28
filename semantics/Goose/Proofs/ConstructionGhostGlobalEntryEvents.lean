import Goose.Proofs.ConstructionGhostGlobalEvents
import Goose.Proofs.ConstructionGhostEntryInitializerEvents

namespace Goose.Proofs.ConstructionGhostGlobalEntryEvents
open Goose.Construct Goose.Proofs.ConstructionExecution
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSourceGlobal Goose.Proofs.ConstructionGhostGlobalStep Goose.Proofs.ConstructionGhostGlobalReplay
open Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostInvocationEventChunks
open Goose.Proofs.ConstructionGhostGlobalEvents Goose.Proofs.ConstructionGhostEntryInitializerEvents
open Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostStatementEvents
open Goose.Proofs.ConstructionGhostResultScope Goose.Proofs.ConstructionGhostModuleInitializerEvents
open Goose.Proofs.ConstructionGhostMaterializedDeclarationEvents

theorem runModule_globalAndEntryEvents (fuel : Nat) (config : EvalConfig) (before : ExecutionState)
    (globalSupported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global),
      config.module.globals[global]? = some descriptor → ∀ environment,
      FuelSupport config (fuel + 3) (.value environment descriptor.init))
    (directSupported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global),
      config.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = true →
      ordinaryProducerCount? (fuel + 3) ⟨config.module, #[]⟩ descriptor.init = none →
      ∀ environment destination, SupportedOperation config (.builder environment destination descriptor.init))
    (context : Context) (implementation : Impl)
    (contextFound : config.module.contexts[config.module.entry]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (parametersEmpty : implementation.params = #[]) (resultsEmpty : implementation.results = #[])
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (body : implementation.body = .mk scope statements tail)
    (entrySupported : ∀ act scopeInst sourceFuel localVar expression origin, .letS localVar expression origin ∈ statements →
      FuelSupport config sourceFuel (.value ⟨context.impl, act, implementation.vars, [(scope, scopeInst)], []⟩ expression)) :
    ∃ globalOutcome globalVisits globalChunks,
      OperandReplay (globalInitializer (fuel + 3) config) 0 (List.range config.module.globals.size) [] before globalOutcome globalVisits ∧
      FixedSourceForest (fuel + 3) config globalVisits ∧ MaterializedSourceForest (fuel + 3) config globalVisits ∧
      DirectSourceForest (fuel + 3) config globalVisits ∧
      globalVisits.map Invocation.operand = (List.range config.module.globals.size).take globalVisits.length ∧
      (globalVisits.map Invocation.ordinal).Nodup ∧ ChunksAlign globalVisits globalChunks ∧
      (Goose.Proofs.Exit.stepState globalOutcome).construction.events = before.construction.events ++ globalChunks.flatten ∧
      runModule (fuel + 3) config before = moduleAfterGlobals (fuel + 3) config (discardGlobalValues globalOutcome) ∧
      ∀ initialized, discardGlobalValues globalOutcome = .ok () initialized →
        runModule (fuel + 3) config before = entryCallResult
          (invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 initialized) ∧
        (initialized.activations.length < Goose.Core.maxCallDepth →
          let activation : RuntimeActivation := ⟨context.impl, initialized.nextAct, implementation.vars, [], []⟩
          let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
          let ready := resultScopeStart activation scope activated
          let scopedEnvironment := { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
          ∃ outcome visits chunks,
            StatementReplay config scopedEnvironment fuel 0 statements ready outcome visits ∧
            visits.map StatementInvocation.statement = statements.take visits.length ∧
            (visits.map StatementInvocation.ordinal).Nodup ∧ ChunksAlign (visits.map statementInvocation) chunks ∧
            (Goose.Proofs.Exit.stepState outcome).construction.events = ready.construction.events ++ chunks.flatten ∧
            FixedVisitSourceEvents config scopedEnvironment visits ∧ MaterializedVisitSourceEvents config scopedEnvironment visits ∧
            invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 initialized =
              ((enterActivation (fuel + 2) config activation [] implementation.body 0 >>= fun carriers =>
                deliverCarriers (fuel + 2) config.layout [] carriers 0) activated)) := by
  obtain ⟨globalOutcome, globalVisits, replay, forest, ordered, once, execution⟩ := runModule_globalReplay (fuel + 3) config before
  obtain ⟨globalChunks, aligned, finalEq, _, _⟩ := replay_eventChunks replay (globalInitializer_keepsEventPrefix (fuel + 3) config)
  have fixed := globalReplay_fuelSourceForest replay (fun global descriptor found _ environment => globalSupported global descriptor found environment)
  have materialized := globalReplay_materializedFuelSourceForest replay (fun global descriptor count found _ _ environment => globalSupported global descriptor found environment)
  refine ⟨globalOutcome, globalVisits, globalChunks, replay, fixed, materialized, globalReplay_directSourceForest replay directSupported,
    ordered, once, aligned, finalEq, execution, ?_⟩
  intro initialized globals
  constructor
  · rw [execution, globals]
    simp only [moduleAfterGlobals, afterGlobals, bind, getImplementation, contextFound, implementationFound, resultsEmpty,
      Array.toList_empty, channelsFor, List.mapM_nil, pure, entryCallResult]
    cases invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 initialized <;> rfl
  · intro depth
    have localSupported : ∀ sourceFuel localVar expression origin, .letS localVar expression origin ∈ statements →
        FuelSupport config sourceFuel (.value ⟨context.impl, initialized.nextAct, implementation.vars, [(scope, initialized.nextScope)], []⟩ expression) := by
      intro sourceFuel localVar expression origin member
      exact entrySupported initialized.nextAct initialized.nextScope sourceFuel localVar expression origin member
    obtain ⟨outcome, visits, chunks, statementReplay, statementOrdered, statementOnce, statementAligned, statementFinal,
      fixedSources, materializedSources, callExecution, enterExecution⟩ :=
      entryCall_initializerEvents fuel config initialized config.module.entry context implementation contextFound implementationFound
        parametersEmpty resultsEmpty depth scope statements tail body localSupported
    exact ⟨outcome, visits, chunks, statementReplay, statementOrdered, statementOnce, statementAligned, statementFinal,
      fixedSources, materializedSources, callExecution⟩

#print axioms runModule_globalAndEntryEvents
end Goose.Proofs.ConstructionGhostGlobalEntryEvents
