import Goose.Proofs.ConstructionGhostGlobalEntryEvents
import Goose.Proofs.ConstructionGhostDirectDeclarationEvents

namespace Goose.Proofs.ConstructionGhostGlobalEntryDirectEvents
open Goose.Construct Goose.Proofs.ConstructionExecution
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSourceGlobal Goose.Proofs.ConstructionGhostGlobalStep Goose.Proofs.ConstructionGhostGlobalReplay
open Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostInvocationEventChunks
open Goose.Proofs.ConstructionGhostGlobalEntryEvents Goose.Proofs.ConstructionGhostDirectDeclarationEvents
open Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostStatementEvents
open Goose.Proofs.ConstructionGhostResultScope Goose.Proofs.ConstructionGhostModuleInitializerEvents
open Goose.Proofs.ConstructionGhostMaterializedDeclarationEvents

theorem runModule_globalAndEntryDirectEvents (fuel : Nat) (config : EvalConfig) (before : ExecutionState)
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
    (parametersEmpty : implementation.params = #[]) (resultsEmpty : implementation.results = #[])
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (body : implementation.body = .mk scope statements tail)
    (entrySupported : ∀ act scopeInst sourceFuel localVar expression origin, .letS localVar expression origin ∈ statements →
      FuelSupport config sourceFuel (.value ⟨context.impl, act, implementation.vars, [(scope, scopeInst)], []⟩ expression))
    (entryBuilderSupported : ∀ act scopeInst sourceFuel localVar expression origin descriptor,
      .letS localVar expression origin ∈ statements → implementation.vars[localVar]? = some descriptor → descriptor.ty.nonfixed = true →
      ordinaryProducerCount? sourceFuel ⟨config.module, implementation.vars⟩ expression = none → ∀ destination, FuelSupport config sourceFuel
        (.builder ⟨context.impl, act, implementation.vars, [(scope, scopeInst)], []⟩ destination expression)) :
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
            DirectVisitSourceEvents config scopedEnvironment visits ∧
            invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 initialized =
              ((enterActivation (fuel + 2) config activation [] implementation.body 0 >>= fun carriers =>
                deliverCarriers (fuel + 2) config.layout [] carriers 0) activated)) := by
  obtain ⟨globalOutcome, globalVisits, globalChunks, globalReplay, globalFixed, globalMaterialized, globalDirect,
    ordered, once, aligned, finalEq, execution, entry⟩ :=
    runModule_globalAndEntryEvents fuel config before globalSupported globalDirectSupported context implementation
      contextFound implementationFound parametersEmpty resultsEmpty scope statements tail body entrySupported
  refine ⟨globalOutcome, globalVisits, globalChunks, globalReplay, globalFixed, globalMaterialized, globalDirect,
    ordered, once, aligned, finalEq, execution, ?_⟩
  intro initialized globals
  obtain ⟨moduleCall, reached⟩ := entry initialized globals
  refine ⟨moduleCall, ?_⟩
  intro depth
  obtain ⟨outcome, visits, chunks, replay, statementOrdered, statementOnce, statementAligned, statementFinal,
    fixedSources, materializedSources, callExecution⟩ := reached depth
  refine ⟨outcome, visits, chunks, replay, statementOrdered, statementOnce, statementAligned, statementFinal,
    fixedSources, materializedSources, ?_, callExecution⟩
  apply statementReplay_directSourceEvents_guarded replay
  intro sourceFuel localVar expression origin descriptor member found nonfixed direct destination
  exact entryBuilderSupported initialized.nextAct initialized.nextScope sourceFuel localVar expression origin descriptor member found nonfixed direct destination

#print axioms runModule_globalAndEntryDirectEvents
end Goose.Proofs.ConstructionGhostGlobalEntryDirectEvents
