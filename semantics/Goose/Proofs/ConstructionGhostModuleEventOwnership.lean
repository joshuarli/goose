import Goose.Proofs.ConstructionGhostEventOwnership
import Goose.Proofs.ConstructionGhostGlobalEvents
import Goose.Proofs.ConstructionGhostActivationResultEvents

namespace Goose.Proofs.ConstructionGhostModuleEventOwnership
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionEventPrefixProtocol Goose.Proofs.ConstructionAcceptedExecution
open Goose.Proofs.ConstructionGhostGlobalReplay Goose.Proofs.ConstructionGhostGlobalEvents Goose.Proofs.ConstructionGhostGlobalStep
open Goose.Proofs.ConstructionGhostSourceGlobal Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostSyntaxFuel
open Goose.Proofs.ConstructionGhostInvocationEventChunks Goose.Proofs.ConstructionGhostEventOwnership
open Goose.Proofs.ConstructionInvocationReplay

attribute [local instance] eventPrefixPrimitives eventPrefixReservationPrimitives

theorem afterGlobals_keepsEventPrefix (fuel : Nat) (config : EvalConfig) : KeepsEventPrefix (afterGlobals fuel config) := by
  intro state
  apply (eventPrefix_iff_isPrefix _ _).mpr
  have kept : PreservesConstructionInvariant (PrefixInvariant state.construction.events) (afterGlobals fuel config) := by
    let previous := evaluation_preservesConstructionInvariant (predicate := PrefixInvariant state.construction.events) fuel config
    unfold afterGlobals
    protocol_eval previous
  exact kept state List.prefix_rfl

theorem moduleAfterGlobals_resultPrefix (fuel : Nat) (config : EvalConfig) (outcome : ExecutionStep Unit) :
    EventPrefix (Goose.Proofs.Exit.stepState outcome).construction.events
      (Goose.Proofs.Exit.stepState (moduleAfterGlobals fuel config outcome)).construction.events := by
  cases outcome with
  | ok value state => cases value; exact afterGlobals_keepsEventPrefix fuel config state
  | stop | escape | jump => exact eventPrefix_refl _

theorem runModule_globalEventOwnership (fuel : Nat) (config : EvalConfig) (before : ExecutionState) :
    ∃ outcome visits chunks continuation,
      OperandReplay (globalInitializer fuel config) 0 (List.range config.module.globals.size) [] before outcome visits ∧
      ChunksAlign visits chunks ∧ OwnsEvents visits chunks ∧
      visits.map Invocation.operand = (List.range config.module.globals.size).take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧
      (Goose.Proofs.Exit.stepState outcome).construction.events = before.construction.events ++ chunks.flatten ∧
      (Goose.Proofs.Exit.stepState (runModule fuel config before)).construction.events =
        before.construction.events ++ chunks.flatten ++ continuation ∧
      (∀ otherChunks, ChunksAlign visits otherChunks → chunks = otherChunks) ∧
      (∀ other, (Goose.Proofs.Exit.stepState (runModule fuel config before)).construction.events =
        (Goose.Proofs.Exit.stepState outcome).construction.events ++ other → continuation = other) := by
  obtain ⟨outcome, visits, replay, forest, ordered, once, execution⟩ := runModule_globalReplay fuel config before
  obtain ⟨chunks, aligned, finalEq, _, _, ownership, unique⟩ :=
    replay_eventOwnership replay (globalInitializer_keepsEventPrefix fuel config)
  have kept := moduleAfterGlobals_resultPrefix fuel config (discardGlobalValues outcome)
  have same : (Goose.Proofs.Exit.stepState (discardGlobalValues outcome)).construction.events =
      (Goose.Proofs.Exit.stepState outcome).construction.events := by cases outcome <;> rfl
  rw [same, ← execution] at kept
  obtain ⟨continuation, continuationEq⟩ := kept
  refine ⟨outcome, visits, chunks, continuation, replay, aligned, ownership, ordered, once, finalEq, ?_, unique, ?_⟩
  · rw [continuationEq, finalEq]
  · intro other otherEq
    exact (List.append_right_inj _).mp (continuationEq.symm.trans otherEq)

theorem runModule_globalSyntaxOwnership (fuel : Nat) (config : EvalConfig) (before : ExecutionState)
    (closed : ClosedModuleWithTails config)
    (globalSyntax : ∀ (global : Goose.Core.GlobalId) (descriptor : Global),
      config.module.globals[global]? = some descriptor → ValueSyntax config descriptor.init)
    (globalBuilderSyntax : ∀ (global : Goose.Core.GlobalId) (descriptor : Global),
      config.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = true →
      ordinaryProducerCount? fuel ⟨config.module, #[]⟩ descriptor.init = none →
      DeclarationBuilderSyntax config descriptor.init) :
    ∃ outcome visits chunks continuation,
      OperandReplay (globalInitializer fuel config) 0 (List.range config.module.globals.size) [] before outcome visits ∧
      FixedSourceForest fuel config visits ∧ MaterializedSourceForest fuel config visits ∧ DirectSourceForest fuel config visits ∧
      ChunksAlign visits chunks ∧ OwnsEvents visits chunks ∧
      visits.map Invocation.operand = (List.range config.module.globals.size).take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧
      (Goose.Proofs.Exit.stepState outcome).construction.events = before.construction.events ++ chunks.flatten ∧
      (Goose.Proofs.Exit.stepState (runModule fuel config before)).construction.events =
        before.construction.events ++ chunks.flatten ++ continuation ∧
      (∀ otherChunks, ChunksAlign visits otherChunks → chunks = otherChunks) ∧
      (∀ other, (Goose.Proofs.Exit.stepState (runModule fuel config before)).construction.events =
        (Goose.Proofs.Exit.stepState outcome).construction.events ++ other → continuation = other) := by
  obtain ⟨outcome, visits, chunks, continuation, replay, aligned, ownership, ordered, once, finalEq, moduleEq, uniqueChunks, uniqueContinuation⟩ :=
    runModule_globalEventOwnership fuel config before
  have fixed := globalReplay_fuelSourceForest replay (fun global descriptor found _ environment =>
    (syntaxFuel_existsWithTails fuel config closed).value environment descriptor.init (globalSyntax global descriptor found))
  have materialized := globalReplay_materializedFuelSourceForest replay (fun global descriptor count found _ _ environment =>
    (syntaxFuel_existsWithTails fuel config closed).value environment descriptor.init (globalSyntax global descriptor found))
  exact ⟨outcome, visits, chunks, continuation, replay, fixed, materialized, globalReplay_directFuelSourceForest replay (fun global descriptor found nonfixed direct environment destination =>
    (syntaxFuel_existsWithTails fuel config closed).builder environment destination descriptor.init
      (globalBuilderSyntax global descriptor found nonfixed direct)),
    aligned, ownership, ordered, once, finalEq, moduleEq, uniqueChunks, uniqueContinuation⟩

theorem runModule_globalSourceOwnership (fuel : Nat) (config : EvalConfig) (before : ExecutionState)
    (closed : ClosedModuleWithTails config)
    (globalSyntax : ∀ (global : Goose.Core.GlobalId) (descriptor : Global),
      config.module.globals[global]? = some descriptor → ValueSyntax config descriptor.init)
    (directSupported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global),
      config.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = true →
      ordinaryProducerCount? fuel ⟨config.module, #[]⟩ descriptor.init = none →
      ∀ environment destination, SupportedOperation config (.builder environment destination descriptor.init)) :
    ∃ outcome visits chunks continuation,
      OperandReplay (globalInitializer fuel config) 0 (List.range config.module.globals.size) [] before outcome visits ∧
      FixedSourceForest fuel config visits ∧ MaterializedSourceForest fuel config visits ∧ DirectSourceForest fuel config visits ∧
      ChunksAlign visits chunks ∧ OwnsEvents visits chunks ∧
      visits.map Invocation.operand = (List.range config.module.globals.size).take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧
      (Goose.Proofs.Exit.stepState outcome).construction.events = before.construction.events ++ chunks.flatten ∧
      (Goose.Proofs.Exit.stepState (runModule fuel config before)).construction.events =
        before.construction.events ++ chunks.flatten ++ continuation ∧
      (∀ otherChunks, ChunksAlign visits otherChunks → chunks = otherChunks) ∧
      (∀ other, (Goose.Proofs.Exit.stepState (runModule fuel config before)).construction.events =
        (Goose.Proofs.Exit.stepState outcome).construction.events ++ other → continuation = other) := by
  apply runModule_globalSyntaxOwnership fuel config before closed globalSyntax
  intro global descriptor found nonfixed direct
  exact .static descriptor.init (directSupported global descriptor found nonfixed direct)

#print axioms runModule_globalSyntaxOwnership
#print axioms runModule_globalSourceOwnership
#print axioms runModule_globalEventOwnership
#print axioms afterGlobals_keepsEventPrefix
#print axioms moduleAfterGlobals_resultPrefix
end Goose.Proofs.ConstructionGhostModuleEventOwnership
