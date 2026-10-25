import Goose.Lower.Validation.StorageSourceControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem StorageAt.loopBody_generated {le : LEnv} {before : LS} (condition : ValueId)
    {body : Nat → BlockId → B ValueId} {back : B Unit}
    (generated : GeneratedBuilderState before)
    (bodyStorage : ∀ depth exit state, GeneratedBuilderState state → exit < state.blocks.size →
      before.blocks.size ≤ state.blocks.size → StorageAt le state (body depth exit))
    (backStorage : ∀ state, StorageAt le state back) :
    StorageAt le before (Goose.Lower.loopBody condition body back) := by
  let forked := Goose.Lower.fork condition le before
  let entered := Goose.Lower.setCur (some forked.1.1) le forked.2
  have forkGenerated := generated.fork condition (show Goose.Lower.fork condition le before = forked from rfl)
  have ids : forked.1 = (before.blocks.size, before.blocks.size + 1) ∧
      forked.2.blocks.size = before.blocks.size + 2 := fork_ids rfl
  have firstBound : forked.1.1 < forked.2.blocks.size := by
    simp only [ids.1, ids.2]
    nat_omega
  have exitBound : forked.1.2 < forked.2.blocks.size := by
    simp only [ids.1, ids.2]
    nat_omega
  have enteredGenerated := forkGenerated.setCur (some forked.1.1)
    (by intro current same; cases same; exact firstBound)
    (show Goose.Lower.setCur _ le forked.2 = entered from rfl)
  have entryBlocks : entered.2.blocks = forked.2.blocks := rfl
  have grows : before.blocks.size ≤ entered.2.blocks.size := by rw [entryBlocks, ids.2]; nat_omega
  unfold Goose.Lower.loopBody
  apply (StorageAt.get _ _).bind
  simp only [get_apply]
  apply (StorageAt.fork _ _ _).bind
  apply (StorageAt.setCur _ _ _).bind
  apply (bodyStorage before.stack.length forked.1.2 entered.2 enteredGenerated
    (by rw [entryBlocks]; exact exitBound) grows).bind
  exact (backStorage _).bind (StorageAt.setCur _ _ _)

theorem StorageAt.lowerWhile_generated {le : LEnv} {before : LS} (header : BlockId)
    {condition : B ValueId} {body : Nat → BlockId → B ValueId}
    (conditionStorage : StorageAt le before condition)
    (conditionGenerated : GeneratedBuilderState (condition le before).2)
    (bodyStorage : ∀ depth exit state, GeneratedBuilderState state → exit < state.blocks.size →
      (condition le before).2.blocks.size ≤ state.blocks.size → StorageAt le state (body depth exit)) :
    StorageAt le before (Goose.Lower.lowerWhile header condition body) := by
  unfold Goose.Lower.lowerWhile
  apply conditionStorage.bind
  apply StorageAt.whenLive
  intro block live
  exact StorageAt.loopBody_generated _ conditionGenerated bodyStorage
    (fun _ => StorageAt.emitTerm _ _ _)

theorem StorageAt.lowerRange_generated {le : LEnv} {before : LS} (type : IntTy) (index bound : ValueId)
    (header : BlockId) {body : Nat → BlockId → B ValueId}
    (generated : GeneratedBuilderState before)
    (bodyStorage : ∀ depth exit state, GeneratedBuilderState state → exit < state.blocks.size →
      (Goose.Lower.emitDef (.cmp .lt type index bound) le before).2.blocks.size ≤ state.blocks.size →
      StorageAt le state (body depth exit)) :
    StorageAt le before (Goose.Lower.lowerRange type index bound header body) := by
  unfold Goose.Lower.lowerRange
  apply (StorageAt.emitDef _ (by intros; trivial)).bind
  exact StorageAt.loopBody_generated _ (generated.emitDef _ rfl) bodyStorage
    (fun _ => StorageAt.rangeBack _ _ _ _ _)

theorem StorageAt.lowerEach_generated {le : LEnv} {before : LS} (regrow : Bool) (owner : Option ValueId)
    (sampled : ValueId) (header : BlockId) (index : ValueId) {body : Nat → BlockId → B ValueId}
    (generated : GeneratedBuilderState before)
    (bodyStorage : ∀ depth exit state, GeneratedBuilderState state → exit < state.blocks.size →
      (Goose.Lower.emitDef (.cmp .lt .i64 index (Goose.Lower.eachLen regrow owner sampled le before).1)
        le (Goose.Lower.eachLen regrow owner sampled le before).2).2.blocks.size ≤ state.blocks.size →
      StorageAt le state (body depth exit)) :
    StorageAt le before (Goose.Lower.lowerEach regrow owner sampled header index body) := by
  unfold Goose.Lower.lowerEach
  apply (StorageAt.eachLen _ _ _ _ _).bind
  apply (StorageAt.emitDef _ (by intros; trivial)).bind
  have lengthGenerated : GeneratedBuilderState (Goose.Lower.eachLen regrow owner sampled le before).2 :=
    generated.eachLen regrow owner sampled rfl
  exact StorageAt.loopBody_generated _ (lengthGenerated.emitDef _ rfl) bodyStorage
    (fun _ => StorageAt.rangeBack _ _ _ _ _)

#print axioms StorageAt.loopBody_generated
#print axioms StorageAt.lowerWhile_generated
#print axioms StorageAt.lowerRange_generated
#print axioms StorageAt.lowerEach_generated

end Goose.Lower.Validation
