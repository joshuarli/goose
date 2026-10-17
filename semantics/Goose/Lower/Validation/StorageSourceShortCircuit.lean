import Goose.Lower.Validation.StorageSourceBranches

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem StorageAt.shortCircuit_generated {le : LEnv} {before : LS} (isAnd : Bool) (condition : ValueId)
    {rhs : B ValueId} (generated : GeneratedBuilderState before)
    (child : ∀ state, GeneratedBuilderState state → StorageAt le state rhs) :
    StorageAt le before (Goose.Lower.shortCircuit isAnd condition rhs) := by
  let forked := Goose.Lower.scFork isAnd condition le before
  let entered := Goose.Lower.setCur (some forked.1.1) le forked.2
  have allocatedGenerated := generated.scFork isAnd condition
    (show Goose.Lower.scFork isAnd condition le before = forked from rfl)
  have ids : forked.1 = (before.blocks.size, before.blocks.size + 1, before.vals.size) ∧
      forked.2.blocks.size = before.blocks.size + 2 := scFork_ids rfl
  have rhsBound : forked.1.1 < forked.2.blocks.size := by
    simp only [ids.1, ids.2]
    nat_omega
  have enteredGenerated := allocatedGenerated.setCur (some forked.1.1)
    (by intro current same; cases same; exact rhsBound)
    (show Goose.Lower.setCur _ le forked.2 = entered from rfl)
  unfold Goose.Lower.shortCircuit
  apply StorageAt.whenLive
  intro block live
  apply (StorageAt.scFork _ _ _ _).bind
  apply (StorageAt.setCur _ _ _).bind
  exact (child entered.2 enteredGenerated).bind ((StorageAt.emitTerm _ _ _).bind
    ((StorageAt.setCur _ _ _).bind (StorageAt.pure _ _ _)))

end Goose.Lower.Validation
