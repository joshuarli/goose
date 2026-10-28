import Goose.Proofs.ConstructionGhostGlobalEvents
import Goose.Proofs.ConstructionBindingEventsCore

namespace Goose.Proofs.ConstructionGhostFixedGlobalEvents
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionAcceptedExecution
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostGlobalStep
open Goose.Proofs.ConstructionGhostGlobalReplay Goose.Proofs.ConstructionGhostInvocation
open Goose.Proofs.ConstructionInvocationReplay

theorem globalAfterValue_events (global : Goose.Core.GlobalId) (source : ExecutionStep Value) :
    (Goose.Proofs.Exit.stepState (globalAfterValue global source)).construction.events =
      (Goose.Proofs.Exit.stepState source).construction.events := by
  cases source with
  | ok value state => exact bindRoot_events (.global global) value state
  | stop | escape | jump => rfl

theorem fixedGlobal_visit_sourceEvents
    (replay : OperandReplay (globalInitializer fuel config) offset globals accumulator before outcome visits)
    (closed : ClosedModuleWithTails config) (visit : Invocation Goose.Core.GlobalId Unit) (member : visit ∈ visits)
    (descriptor : Global) (found : config.module.globals[visit.operand]? = some descriptor)
    (fixed : descriptor.ty.nonfixed = false) (derivation : ValueSyntax config descriptor.init) :
    let environment : RuntimeActivation := ⟨0, visit.before.nextAct, #[], [], []⟩
    let ready := { visit.before with nextAct := visit.before.nextAct + 1 }
    SourceHistory config fuel [visit.ordinal, 0] (.value environment descriptor.init) ready
      (evalValue fuel config environment descriptor.init ready) ∧
    ready.construction.events = visit.before.construction.events ∧
    (Goose.Proofs.Exit.stepState visit.outcome).construction.events =
      (Goose.Proofs.Exit.stepState (evalValue fuel config environment descriptor.init ready)).construction.events ∧
    EventPrefix visit.before.construction.events (Goose.Proofs.Exit.stepState visit.outcome).construction.events := by
  dsimp only
  obtain ⟨tree, executed⟩ := fixedGlobal_initializer_ghost fuel config [visit.ordinal] visit.operand visit.before descriptor found fixed
  have actual := (visit_executes replay visit member).symm.trans executed
  refine ⟨fuelHistory_exists fuel config _ _ _
    ((syntaxFuel_existsWithTails fuel config closed).value _ descriptor.init derivation), rfl, ?_, ?_⟩
  · rw [actual]
    exact globalAfterValue_events visit.operand _
  · rw [actual, globalAfterValue_events]
    exact (evaluation_keepsEventPrefix fuel config).value _ descriptor.init _

theorem runModule_fixedGlobalSourceEvents (fuel : Nat) (config : EvalConfig) (before : ExecutionState)
    (closed : ClosedModuleWithTails config)
    (globalSyntax : ∀ (global : Goose.Core.GlobalId) (descriptor : Global),
      config.module.globals[global]? = some descriptor → ValueSyntax config descriptor.init) :
    ∃ outcome visits,
      OperandReplay (globalInitializer fuel config) 0 (List.range config.module.globals.size) [] before outcome visits ∧
      visits.map Invocation.operand = (List.range config.module.globals.size).take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧
      runModule fuel config before = moduleAfterGlobals fuel config (discardGlobalValues outcome) ∧
      ∀ visit ∈ visits, ∀ descriptor, config.module.globals[visit.operand]? = some descriptor → descriptor.ty.nonfixed = false →
        let environment : RuntimeActivation := ⟨0, visit.before.nextAct, #[], [], []⟩
        let ready := { visit.before with nextAct := visit.before.nextAct + 1 }
        SourceHistory config fuel [visit.ordinal, 0] (.value environment descriptor.init) ready
          (evalValue fuel config environment descriptor.init ready) ∧
        (Goose.Proofs.Exit.stepState visit.outcome).construction.events =
          (Goose.Proofs.Exit.stepState (evalValue fuel config environment descriptor.init ready)).construction.events := by
  obtain ⟨outcome, visits, replay, forest, ordered, once, execution⟩ := runModule_globalReplay fuel config before
  refine ⟨outcome, visits, replay, ordered, once, execution, ?_⟩
  intro visit member descriptor found fixed
  obtain ⟨history, initial, final, retained⟩ :=
    fixedGlobal_visit_sourceEvents replay closed visit member descriptor found fixed (globalSyntax visit.operand descriptor found)
  exact ⟨history, final⟩

#print axioms runModule_fixedGlobalSourceEvents
#print axioms globalAfterValue_events
#print axioms fixedGlobal_visit_sourceEvents
end Goose.Proofs.ConstructionGhostFixedGlobalEvents
