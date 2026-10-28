import Goose.Proofs.ConstructionGhostCallSetupHistory
import Goose.Proofs.ConstructionGhostGlobalEvents

namespace Goose.Proofs.ConstructionGhostModuleSetupHistory
open Goose.Construct Goose.Proofs.ConstructionGhostCallSetupHistory Goose.Proofs.ConstructionGhostCallSetup
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostSourceGlobal
open Goose.Proofs.ConstructionGhostGlobalStep Goose.Proofs.ConstructionGhostGlobalReplay
open Goose.Proofs.ConstructionInvocationReplay

theorem moduleAfterGlobals_channelTerminal (fuel : Nat) (config : EvalConfig) (initialized : ExecutionState)
    (context : Context) (implementation : Impl) (terminal : ExecutionStep (List Carrier))
    (contextFound : config.module.contexts[config.module.entry]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (prepared : terminalCall (channelsFor config.layout 0 implementation.results.toList 0 initialized) = some terminal) :
    moduleAfterGlobals fuel config (.ok () initialized) = entryCallResult terminal := by
  simp only [moduleAfterGlobals, afterGlobals, bind, getImplementation, contextFound, implementationFound, pure]
  cases result : channelsFor config.layout 0 implementation.results.toList 0 initialized <;>
    simp_all [terminalCall, entryCallResult, bind]
  all_goals subst terminal <;> rfl

theorem runModule_entrySetupHistory (fuel : Nat) (config : EvalConfig) (before : ExecutionState)
    (closed : ClosedModuleWithTails config) (context : Context) (implementation : Impl)
    (contextFound : config.module.contexts[config.module.entry]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (entryArguments : ∀ id actual start ready,
      getImplementation config config.module.entry start = .ok (id, actual) ready →
      ArgumentSyntax config actual.params.toList []) :
    ∃ globalOutcome globalVisits,
      OperandReplay (globalInitializer (fuel + 1) config) 0 (List.range config.module.globals.size) [] before globalOutcome globalVisits ∧
      runModule (fuel + 1) config before = moduleAfterGlobals (fuel + 1) config (discardGlobalValues globalOutcome) ∧
      ∀ initialized channels callReady, discardGlobalValues globalOutcome = .ok () initialized →
        channelsFor config.layout 0 implementation.results.toList 0 initialized = .ok channels callReady →
        CallSetupHistory fuel config ⟨0, 0, #[], [], []⟩ [config.module.globals.size, 0]
          config.module.entry [] channels 0 callReady ∧
        runModule (fuel + 1) config before = entryCallResult
          (invokeCall (fuel + 1) config ⟨0, 0, #[], [], []⟩ config.module.entry [] channels 0 callReady) := by
  obtain ⟨globalOutcome, globalVisits, replay, forest, ordered, once, execution⟩ := runModule_globalReplay (fuel + 1) config before
  refine ⟨globalOutcome, globalVisits, replay, execution, ?_⟩
  intro initialized channels callReady globals prepared
  constructor
  · exact invokeCall_validatedSetupHistory fuel config ⟨0, 0, #[], [], []⟩ [config.module.globals.size, 0]
      config.module.entry [] channels 0 callReady closed entryArguments
  · rw [execution, globals]
    simp only [moduleAfterGlobals, afterGlobals, bind, getImplementation, contextFound, implementationFound,
      pure, prepared, entryCallResult]
    cases invokeCall (fuel + 1) config ⟨0, 0, #[], [], []⟩ config.module.entry [] channels 0 callReady <;> rfl

#print axioms moduleAfterGlobals_channelTerminal
#print axioms runModule_entrySetupHistory
end Goose.Proofs.ConstructionGhostModuleSetupHistory
