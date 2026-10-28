import Goose.Proofs.ConstructionExitNamedStoredCount
import Goose.Proofs.ConstructionAcceptedBindings

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem bind_built_destination_alias (state : ExecutionState) (root : RootInst) (id count : Nat)
    (row : PendingDestination) (present : state.construction.destinations[id]? = some row)
    (built : row.progress = .built count) :
    ∃ stored after, storedDestination id state = .ok stored state ∧
      bindRoot root (.stored stored) state = .ok () after ∧
      after.objects.lookup root = some (.stored stored) ∧
      stored.destination = some id ∧ stored.count = count ∧ after.construction = state.construction ∧
      storedDestination id after = .ok stored after := by
  let stored : StoredValue := ⟨row.storage, row.capability.start, row.capability.logicalType, count, some id, none, [], count⟩
  have sampled : storedDestination id state = .ok stored state := by
    simp only [storedDestination, getDestination, EvalM.get, present, bind, built, progressCount, pure]
    rfl
  cases ordinal : state.objectOrdinals.lookup root with
  | none =>
    let after := { state with
      objects := (root, .stored stored) :: state.objects.filter (fun entry => entry.1 != root)
      objectOrdinals := (root, stored.object.getD stored.storage) :: state.objectOrdinals.filter (fun entry => entry.1 != root) }
    refine ⟨stored, after, sampled, ?_, ?_, rfl, rfl, rfl, ?_⟩
    · simp [bindRoot, ordinal, setObjectOrdinal, bindStaticRoot, EvalM.get, EvalM.set, bind, after]
    · simp [after, List.lookup]
    · simp [after, storedDestination, getDestination, EvalM.get, present, bind, built, progressCount, pure, stored]
  | some old =>
    let after := { state with objects := (root, .stored stored) :: state.objects.filter (fun entry => entry.1 != root) }
    refine ⟨stored, after, sampled, ?_, ?_, rfl, rfl, rfl, ?_⟩
    · simp [bindRoot, ordinal, bindStaticRoot, EvalM.get, EvalM.set, bind, after]
    · simp [after, List.lookup]
    · simp [after, storedDestination, getDestination, EvalM.get, present, bind, built, progressCount, pure, stored]

#print axioms bind_built_destination_alias

end Goose.Proofs.ConstructionAcceptedExecution
