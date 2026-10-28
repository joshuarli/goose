import Goose.Proofs.ConstructionGhostDeclarationReplay
import Goose.Proofs.ConstructionGhostGlobalChannelEntryEvents

namespace Goose.Proofs.ConstructionGhostDeclarationModule
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostGlobalStep Goose.Proofs.ConstructionGhostGlobalReplay Goose.Proofs.ConstructionGhostSourceGlobal
open Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostStatements
open Goose.Proofs.ConstructionGhostChannelEntryEvents Goose.Proofs.ConstructionGhostGlobalChannelEntryEvents
open Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostCallActivation
open Goose.Proofs.ConstructionGhostResultScope Goose.Proofs.ConstructionGhostSyntaxFuel
open Goose.Proofs.ConstructionGhostDeclarationReplay

theorem runModule_declarationVisits (fuel : Nat) (config : EvalConfig) (before : ExecutionState)
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
    (closed : ClosedModuleWithTails config) (statementSyntax : ∀ statement ∈ statements, StatementSyntax config statement)
 :
    ∃ globalOutcome globalVisits,
      OperandReplay (globalInitializer (fuel + 3) config) 0 (List.range config.module.globals.size) [] before globalOutcome globalVisits ∧
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
          ∃ outcome visits,
            StatementReplay config scopedEnvironment fuel 0 statements ready outcome visits ∧
            (visits.map StatementInvocation.ordinal).Nodup ∧
            (∀ visit ∈ visits, ∀ sourceFuel localVar expression origin,
              visit.fuel = sourceFuel + 1 → visit.statement = .letS localVar expression origin →
              VisitClassification config scopedEnvironment visit sourceFuel localVar expression origin) ∧
            invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] channels 0 callReady =
              ((enterActivation (fuel + 2) config activation [] implementation.body 0 >>= fun carriers =>
                deliverCarriers (fuel + 2) config.layout channels carriers 0) activated) := by
  have entrySupported : ∀ act scopeInst channels sourceFuel localVar expression origin,
      .letS localVar expression origin ∈ statements →
      FuelSupport config sourceFuel (.value ⟨context.impl, act, implementation.vars, [(scope, scopeInst)], channels⟩ expression) := by
    intro act scopeInst channels sourceFuel localVar expression origin member
    have derivation := statementSyntax (.letS localVar expression origin) member
    cases derivation with
    | declaration _ _ _ value _ => exact (syntaxFuel_existsWithTails sourceFuel config closed).value _ expression value
  have entryBuilderSupported : ∀ act scopeInst channels sourceFuel localVar expression origin descriptor,
      .letS localVar expression origin ∈ statements → implementation.vars[localVar]? = some descriptor → descriptor.ty.nonfixed = true →
      ∀ destination, FuelSupport config sourceFuel
        (.builder ⟨context.impl, act, implementation.vars, [(scope, scopeInst)], channels⟩ destination expression) := by
    intro act scopeInst channels sourceFuel localVar expression origin descriptor member found nonfixed destination
    have derivation := statementSyntax (.letS localVar expression origin) member
    cases derivation with
    | declaration _ _ _ value builder =>
        cases builder with
        | bytes ty bytes byteOrigin => exact .legacy sourceFuel (.builderBytes _ destination ty bytes byteOrigin)
        | scalar expression shape source => exact (syntaxFuel_existsWithTails sourceFuel config closed).scalarBuilder _ destination expression shape source
        | supported expression source => exact (syntaxFuel_existsWithTails sourceFuel config closed).supportedBuilder _ destination expression source
        | static expression source => exact .legacy sourceFuel (source _ destination)
  obtain ⟨globalOutcome, globalVisits, globalChunks, replay, fixed, materialized, direct, ordered, once, aligned, finalEq, execution, entry⟩ :=
    runModule_globalAndChannelEntryEvents fuel config before globalSupported globalDirectSupported context implementation
      contextFound implementationFound parametersEmpty scope statements tail body entrySupported entryBuilderSupported
  refine ⟨globalOutcome, globalVisits, replay, execution, ?_⟩
  intro initialized channels callReady globals channelResult
  obtain ⟨callExecution, reached⟩ := entry initialized channels callReady globals channelResult
  refine ⟨callExecution, ?_⟩
  intro callable argumentsReady refreshed activationReady prepared refresh depth
  obtain ⟨outcome, visits, chunks, statementReplay, statementOrdered, statementOnce, statementAligned, statementFinal,
    fixedSources, materializedSources, directSources, namedSources, activationExecution⟩ :=
      reached callable argumentsReady refreshed activationReady prepared refresh depth
  refine ⟨outcome, visits, statementReplay, statementOnce, ?_, activationExecution⟩
  intro visit member sourceFuel localVar expression origin visitFuel visitStatement
  have inMapped : visit.statement ∈ visits.map StatementInvocation.statement := List.mem_map_of_mem member
  rw [statementOrdered] at inMapped
  have inStatements : visit.statement ∈ statements := List.mem_of_mem_take inMapped
  exact declaration_visit_classification statementReplay visit member sourceFuel localVar expression origin visitFuel visitStatement
    closed (statementSyntax visit.statement inStatements)

#print axioms runModule_declarationVisits
end Goose.Proofs.ConstructionGhostDeclarationModule
