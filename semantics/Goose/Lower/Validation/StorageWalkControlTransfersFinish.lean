import Goose.Lower.Validation.StorageWalkControlLoops
import Goose.Lower.Validation.StorageWalkControlTransfers

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem StorageWalkAction.finishFunction (slots : Array Slot) (impl : Impl) (value : ValueId) :
    StorageWalkAction slots [] none (Goose.Lower.finishFunction impl value) := by
  unfold Goose.Lower.finishFunction
  refine (StorageWalkAction.read slots [] none).bind fun env =>
    (StorageWalkAction.isLive slots [] none).bind fun live => ?_
  cases live <;> simp only [Bool.false_eq_true, reduceIte]
  · exact StorageWalkAction.pure slots [] none _
  · split
    · apply StorageWalkAction.header [] [] advB_newBlock0
        (fun sink _ => Goose.Lower.emitTerm (.br sink []))
        (fun sink _ => advB_emitTerm (.br sink []))
      intro sink params env before entry exit config context stackEq current target bound result after run
      have closed := config.emitTerm (.br sink []) rfl env (by
        intro destination member
        have same : destination = sink := by simpa [Term.successors] using member
        subst destination
        exact target) (by
        intro destination member
        have same : destination = sink := by simpa [Term.successors] using member
        subst destination
        exact bound)
      rw [run] at closed
      exact ⟨entry, exit, closed, ScopeMapAdvance.refl _ _ _⟩
    · exact StorageWalkAction.emitReturn slots none _ none

#print axioms StorageWalkAction.finishFunction

end Goose.Lower.Validation
