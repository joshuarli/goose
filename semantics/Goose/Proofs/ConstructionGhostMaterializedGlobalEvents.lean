import Goose.Proofs.ConstructionGhostFixedGlobalEvents

namespace Goose.Proofs.ConstructionGhostMaterializedGlobalEvents
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionEventPrefixProtocol Goose.Proofs.ConstructionAcceptedExecution
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostGlobalStep Goose.Proofs.ConstructionGhostGlobalReplay
open Goose.Proofs.ConstructionGhostInvocation Goose.Proofs.ConstructionGhostMaterialization
open Goose.Proofs.ConstructionInvocationReplay

attribute [local instance] eventPrefixPrimitives eventPrefixReservationPrimitives

theorem nonfixedGlobalContinuation_keepsEventPrefix (fuel : Nat) (config : EvalConfig)
    (global : Goose.Core.GlobalId) (descriptor : Global) (act : Goose.Core.ActId) (materialized : Option (Array Value)) :
    KeepsEventPrefix (nonfixedGlobalContinuation fuel config global descriptor act materialized) := by
  intro before
  apply (eventPrefix_iff_isPrefix _ _).mpr
  have preserved : PreservesConstructionInvariant (PrefixInvariant before.construction.events)
      (nonfixedGlobalContinuation fuel config global descriptor act materialized) := by
    have tail : ∀ carrier : Carrier, PreservesConstructionInvariant (PrefixInvariant before.construction.events)
        (do let value ← carrierValue carrier; bindRoot (.global global) value) := by
      intro carrier
      apply preservesConstructionInvariant_bind
      · exact stateQuery_preservesConstructionInvariant _ (stateQuery_carrierValue carrier)
      · intro value; exact preservesConstructionInvariant_bindRoot _ _
    unfold nonfixedGlobalContinuation
    cases materialized with
    | none =>
        apply preservesConstructionInvariant_bind
        · apply preservesConstructionInvariant_constructLocal
          intro destination
          exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before.construction.events) fuel config).build _ destination _
        · exact tail
    | some values =>
        apply preservesConstructionInvariant_bind
        · exact preservesConstructionInvariant_materializedDestination (predicate := PrefixInvariant before.construction.events) _ _ _ _ _ _ _
        · intro destination
          apply preservesConstructionInvariant_bind
          · exact preservesConstructionInvariant_publishCarriers _ _
          · intro ignored
            apply preservesConstructionInvariant_bind
            · exact preservesConstructionInvariant_pure _
            · exact tail
  exact preserved before List.prefix_rfl

theorem materializedGlobal_visit_sourceEvents
    (replay : OperandReplay (globalInitializer fuel config) offset globals accumulator before outcome visits)
    (visit : Invocation Goose.Core.GlobalId Unit) (member : visit ∈ visits) (descriptor : Global) (count : Nat)
    (found : config.module.globals[visit.operand]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
    (materialized : ordinaryProducerCount? fuel ⟨config.module, #[]⟩ descriptor.init = some count)
    (supported : FuelSupport config fuel (.value ⟨0, visit.before.nextAct, #[], [], []⟩ descriptor.init)) :
    let environment : RuntimeActivation := ⟨0, visit.before.nextAct, #[], [], []⟩
    let ready := { visit.before with nextAct := visit.before.nextAct + 1 }
    SourceHistory config fuel [visit.ordinal, 0] (.value environment descriptor.init) ready
      (evalValue fuel config environment descriptor.init ready) ∧
    ready.construction.events = visit.before.construction.events ∧
    EventPrefix (Goose.Proofs.Exit.stepState (evalValue fuel config environment descriptor.init ready)).construction.events
      (Goose.Proofs.Exit.stepState visit.outcome).construction.events := by
  dsimp only
  obtain ⟨tree, execution⟩ := materializedGlobal_initializer_ghost fuel config [visit.ordinal] visit.operand visit.before descriptor count found nonfixed materialized
  have actual := (visit_executes replay visit member).symm.trans execution
  refine ⟨fuelHistory_exists fuel config _ _ _ supported, rfl, ?_⟩
  rw [actual]
  cases source : evalValue fuel config ⟨0, visit.before.nextAct, #[], [], []⟩ descriptor.init
      { visit.before with nextAct := visit.before.nextAct + 1 } with
  | ok value state =>
      cases value <;> simp only [source, materializationContinuation, globalAfterMaterialization, Goose.Proofs.Exit.stepState]
      all_goals first
        | exact nonfixedGlobalContinuation_keepsEventPrefix fuel config visit.operand descriptor visit.before.nextAct _ _
        | exact eventPrefix_refl _
  | stop | escape | jump => simp [source, materializationContinuation, globalAfterMaterialization, Goose.Proofs.Exit.stepState, eventPrefix_refl]

#print axioms nonfixedGlobalContinuation_keepsEventPrefix
#print axioms materializedGlobal_visit_sourceEvents
end Goose.Proofs.ConstructionGhostMaterializedGlobalEvents
