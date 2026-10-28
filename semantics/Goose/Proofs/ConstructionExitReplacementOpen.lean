import Goose.Proofs.ConstructionExecutionOwnershipLinkAllocation

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem open_replacement_parent_exact (state final : ConstructionState) (parentId selected count : Nat)
    (row : PendingDestination) (present : state.destinations[parentId]? = some row)
    (opened : row.progress = .open count)
    (executed : openExitReplacement parentId state = .ok selected final) :
    final.destinations[parentId]? = some { row with progress := .exiting count selected } := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  simp only [openExitReplacement, writableDestination_result, present, bind] at executed
  cases allowed : destinationCanWrite state parentId with
  | false => simp [allowed] at executed
  | true =>
    simp only [allowed, opened, pure, bind, lookupStorage_result] at executed
    cases stored : state.storage[row.storage]? with
    | none => simp [stored] at executed
    | some storage =>
      have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
      simp only [stored, bind, ConstructionM.get, ConstructionM.set, pure,
        replaceDestination_result, replaceStorage_result, emit_result,
        Array.size_push, Nat.lt_succ_of_lt inside, storageInside,
        Array.size_setIfInBounds, ↓reduceIte] at executed
      split at executed <;>
        simp only [Nat.lt_succ_of_lt inside, storageInside, ↓reduceIte, bind, pure] at executed <;>
        cases executed <;>
        simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self,
          Nat.lt_succ_of_lt inside]

#print axioms open_replacement_parent_exact

end Goose.Proofs.ConstructionAcceptedExecution
