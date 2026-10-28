import Goose.Proofs.ConstructionGhostSourceGlobal
import Goose.Proofs.ConstructionGhostSyntaxFuel
import Goose.Proofs.ConstructionGhostInvocationEventChunks

namespace Goose.Proofs.ConstructionGhostGlobalEvents
open Goose.Construct Goose.Proofs.ConstructionExecution
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostSourceGlobal
open Goose.Proofs.ConstructionGhostGlobalStep Goose.Proofs.ConstructionGhostGlobalReplay
open Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostInvocationEventChunks

theorem globalInitializer_keepsEventPrefix (fuel : Nat) (config : EvalConfig) (global : Goose.Core.GlobalId) :
    KeepsEventPrefix (globalInitializer fuel config global) := by
  intro before
  have preserved := initGlobals_keepsEventPrefix fuel config [global] before
  have same : initGlobals fuel config [global] before = globalInitializer fuel config global before := by
    rw [initGlobals_step]
    simp only [initGlobals, bind, pure]
    cases globalInitializer fuel config global before <;> rfl
  rw [same] at preserved
  exact preserved

theorem runModule_globalEventChunks (fuel : Nat) (config : EvalConfig) (before : ExecutionState)
    (closed : ClosedModuleWithTails config)
    (globalSyntax : ∀ (global : Goose.Core.GlobalId) (descriptor : Global),
      config.module.globals[global]? = some descriptor → ValueSyntax config descriptor.init)
    (directSupported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global),
      config.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = true →
      ordinaryProducerCount? fuel ⟨config.module, #[]⟩ descriptor.init = none →
      ∀ environment destination, SupportedOperation config (.builder environment destination descriptor.init))
    (entryContext : Context) (entryImplementation : Impl)
    (entryFound : config.module.contexts[config.module.entry]? = some entryContext)
    (entryImplementationFound : config.module.impls[entryContext.impl]? = some entryImplementation)
    (entryArgumentSyntax : ∀ id implementation start lookupReady,
      getImplementation config config.module.entry start = .ok (id, implementation) lookupReady →
      ArgumentSyntax config implementation.params.toList []) :
    ∃ outcome visits chunks,
      OperandReplay (globalInitializer fuel config) 0 (List.range config.module.globals.size) [] before outcome visits ∧
      FixedSourceForest fuel config visits ∧ MaterializedSourceForest fuel config visits ∧ DirectSourceForest fuel config visits ∧
      visits.map Invocation.operand = (List.range config.module.globals.size).take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧ ChunksAlign visits chunks ∧
      (Goose.Proofs.Exit.stepState outcome).construction.events = before.construction.events ++ chunks.flatten ∧
      runModule fuel config before = moduleAfterGlobals fuel config (discardGlobalValues outcome) ∧
      ∀ initialized channels ready, discardGlobalValues outcome = .ok () initialized →
        channelsFor config.layout 0 entryImplementation.results.toList 0 initialized = .ok channels ready →
        SourceHistory config fuel [config.module.globals.size, 0]
          (.channelCall ⟨0, 0, #[], [], []⟩ config.module.entry [] channels 0) ready
          (invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] channels 0 ready) ∧
        runModule fuel config before = entryCallResult
          (invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] channels 0 ready) := by
  obtain ⟨outcome, visits, replay, forest, ordered, once, execution⟩ := runModule_globalReplay fuel config before
  obtain ⟨chunks, aligned, finalEq, _, _⟩ := replay_eventChunks replay (globalInitializer_keepsEventPrefix fuel config)
  refine ⟨outcome, visits, chunks, replay, ?_, ?_, globalReplay_directSourceForest replay directSupported,
    ordered, once, aligned, finalEq, execution, ?_⟩
  · apply globalReplay_fuelSourceForest replay
    intro global descriptor found fixed environment
    exact (syntaxFuel_existsWithTails fuel config closed).value environment descriptor.init (globalSyntax global descriptor found)
  · apply globalReplay_materializedFuelSourceForest replay
    intro global descriptor count found nonfixed materialized environment
    exact (syntaxFuel_existsWithTails fuel config closed).value environment descriptor.init (globalSyntax global descriptor found)

  · intro initialized channels ready globals prepared
    refine ⟨fuelHistory_exists fuel config _ _ ready
      ((syntaxFuel_existsWithTails fuel config closed).channelCall ⟨0, 0, #[], [], []⟩ config.module.entry [] channels 0 entryArgumentSyntax), ?_⟩
    rw [execution, globals]
    simp only [moduleAfterGlobals, afterGlobals, bind, getImplementation, entryFound, entryImplementationFound,
      pure, prepared, entryCallResult]
    cases invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] channels 0 ready <;> rfl

#print axioms globalInitializer_keepsEventPrefix
#print axioms runModule_globalEventChunks
end Goose.Proofs.ConstructionGhostGlobalEvents
