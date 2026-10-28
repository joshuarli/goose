import Goose.Proofs.ConstructionAcceptedEntryBytePrefix

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

def FutureGlobalsClear (config : EvalConfig) (initialized : Nat) (state : ExecutionState) : Prop :=
  ∀ id, initialized ≤ id → id < config.module.globals.size →
    state.objects.lookup (.global id) = none ∧ state.objectOrdinals.lookup (.global id) = none

theorem futureGlobalsClear_initial (config : EvalConfig) : FutureGlobalsClear config 0 .initial := by
  intro id future inside
  exact ⟨rfl, rfl⟩

theorem FutureGlobalsClear.freshAct {config : EvalConfig} {initialized : Nat} {state : ExecutionState}
    (clear : FutureGlobalsClear config initialized state) :
    FutureGlobalsClear config initialized { state with nextAct := state.nextAct + 1 } := clear

theorem FutureGlobalsClear.freshDestination {config : EvalConfig} {initialized : Nat} {before after : ExecutionState}
    (clear : FutureGlobalsClear config initialized before) (frame : FreshDestinationFrame before after) :
    FutureGlobalsClear config initialized after := by
  intro id future inside
  rw [frame.outer]
  exact clear id future inside

theorem FutureGlobalsClear.bindGlobal {config : EvalConfig} {initialized : Nat} {before after : ExecutionState}
    (clear : FutureGlobalsClear config initialized before) (value : Value)
    (bound : bindRoot (.global initialized) value before = .ok () after) :
    FutureGlobalsClear config (initialized + 1) after := by
  intro id future inside
  have different : Goose.Core.RootInst.global id ≠ .global initialized := by
    intro same
    have equal : id = initialized := Goose.Core.RootInst.global.inj same
    omega
  obtain ⟨objects, ordinals⟩ := clear id (by omega) inside
  exact ⟨(bindRoot_lookup_other _ _ value before after bound different).trans objects,
    (bindRoot_ordinals_other _ _ value before after bound different).trans ordinals⟩

#print axioms futureGlobalsClear_initial
#print axioms FutureGlobalsClear.freshAct
#print axioms FutureGlobalsClear.freshDestination
#print axioms FutureGlobalsClear.bindGlobal

end Goose.Proofs.ConstructionAcceptedExecution
