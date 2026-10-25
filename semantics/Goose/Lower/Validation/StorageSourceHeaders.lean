import Goose.Lower.Validation.StorageSourceBranches

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem StorageAt.header_generated {le : LEnv} {before : LS} (types : List VTy) (arguments : List ValueId)
    {tail : BlockId → List ValueId → B α} (generated : GeneratedBuilderState before)
    (child : ∀ header parameters state, GeneratedBuilderState state → header < state.blocks.size →
      StorageAt le state (tail header parameters)) :
    StorageAt le before (do
      let (header, parameters) ← Goose.Lower.newBlock types
      Goose.Lower.emitTerm (.br header arguments)
      Goose.Lower.setCur (some header)
      tail header parameters) := by
  let allocated := Goose.Lower.newBlock types le before
  let closed := Goose.Lower.emitTerm (.br allocated.1.1 arguments) le allocated.2
  let entered := Goose.Lower.setCur (some allocated.1.1) le closed.2
  have allocatedGenerated := generated.newBlock types
    (show Goose.Lower.newBlock types le before = allocated from rfl)
  have id : allocated.1.1 = before.blocks.size := by simp [allocated, newBlock_run_general]
  have size : allocated.2.blocks.size = before.blocks.size + 1 := by simp [allocated, newBlock_run_general]
  have bound : allocated.1.1 < allocated.2.blocks.size := by rw [id, size]; nat_omega
  have closedGenerated := allocatedGenerated.emitTerm (.br allocated.1.1 arguments)
    (by intro target member; have same : target = allocated.1.1 := by simpa [Term.successors] using member
        rw [same]; exact bound)
    (show Goose.Lower.emitTerm _ le allocated.2 = closed from rfl)
  have closedFacts := dense_emitTerm (.br allocated.1.1 arguments) le allocated.2 closed.1 closed.2 rfl
    allocatedGenerated.dense allocatedGenerated.live
  have laterBound := Nat.lt_of_lt_of_le bound closedFacts.2.2
  have enteredGenerated := closedGenerated.setCur (some allocated.1.1)
    (by intro current same; cases same; exact laterBound)
    (show Goose.Lower.setCur _ le closed.2 = entered from rfl)
  apply (StorageAt.newBlock _ _ _).bind
  apply (StorageAt.emitTerm _ _ _).bind
  apply (StorageAt.setCur _ _ _).bind
  exact child allocated.1.1 allocated.1.2 entered.2 enteredGenerated laterBound

end Goose.Lower.Validation
