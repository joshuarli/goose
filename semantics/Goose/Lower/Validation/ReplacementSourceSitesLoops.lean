import Goose.Lower.Validation.ReplacementSourceSitesControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ReplacementSitesAt.loopBody_generated {le : LEnv} {before : LS} (condition : ValueId)
    {body : Nat → BlockId → B ValueId} {back : B Unit}
    (generated : GeneratedBuilderState before)
    (bodyStorage : ∀ depth exit state, GeneratedBuilderState state → exit < state.blocks.size →
      before.blocks.size ≤ state.blocks.size → ReplacementSitesAt le state (body depth exit))
    (backStorage : ∀ state, ReplacementSitesAt le state back) :
    ReplacementSitesAt le before (Goose.Lower.loopBody condition body back) := by
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
  apply (ReplacementSitesAt.get _ _).bind
  simp only [get_apply]
  apply (ReplacementSitesAt.fork _ _ _).bind
  apply (ReplacementSitesAt.setCur _ _ _).bind
  apply (bodyStorage before.stack.length forked.1.2 entered.2 enteredGenerated
    (by rw [entryBlocks]; exact exitBound) grows).bind
  exact (backStorage _).bind (ReplacementSitesAt.setCur _ _ _)

theorem ReplacementSitesAt.lowerWhile_generated {le : LEnv} {before : LS} (header : BlockId)
    {condition : B ValueId} {body : Nat → BlockId → B ValueId}
    (conditionStorage : ReplacementSitesAt le before condition)
    (conditionGenerated : GeneratedBuilderState (condition le before).2)
    (bodyStorage : ∀ depth exit state, GeneratedBuilderState state → exit < state.blocks.size →
      (condition le before).2.blocks.size ≤ state.blocks.size → ReplacementSitesAt le state (body depth exit)) :
    ReplacementSitesAt le before (Goose.Lower.lowerWhile header condition body) := by
  unfold Goose.Lower.lowerWhile
  apply conditionStorage.bind
  apply ReplacementSitesAt.whenLive
  intro block live
  exact ReplacementSitesAt.loopBody_generated _ conditionGenerated bodyStorage
    (fun _ => ReplacementSitesAt.emitTerm _ _ _)

theorem ReplacementSitesAt.lowerRange_generated {le : LEnv} {before : LS} (type : IntTy) (index bound : ValueId)
    (header : BlockId) {body : Nat → BlockId → B ValueId}
    (generated : GeneratedBuilderState before)
    (bodyStorage : ∀ depth exit state, GeneratedBuilderState state → exit < state.blocks.size →
      (Goose.Lower.emitDef (.cmp .lt type index bound) le before).2.blocks.size ≤ state.blocks.size →
      ReplacementSitesAt le state (body depth exit)) :
    ReplacementSitesAt le before (Goose.Lower.lowerRange type index bound header body) := by
  unfold Goose.Lower.lowerRange
  apply (ReplacementSitesAt.emitDef _ (by intros; trivial)).bind
  exact ReplacementSitesAt.loopBody_generated _ (generated.emitDef _ rfl) bodyStorage
    (fun _ => ReplacementSitesAt.rangeBack _ _ _ _ _)

theorem ReplacementSitesAt.lowerEach_generated {le : LEnv} {before : LS} (regrow : Bool) (owner : Option ValueId)
    (sampled : ValueId) (header : BlockId) (index : ValueId) {body : Nat → BlockId → B ValueId}
    (generated : GeneratedBuilderState before)
    (bodyStorage : ∀ depth exit state, GeneratedBuilderState state → exit < state.blocks.size →
      (Goose.Lower.emitDef (.cmp .lt .i64 index (Goose.Lower.eachLen regrow owner sampled le before).1)
        le (Goose.Lower.eachLen regrow owner sampled le before).2).2.blocks.size ≤ state.blocks.size →
      ReplacementSitesAt le state (body depth exit)) :
    ReplacementSitesAt le before (Goose.Lower.lowerEach regrow owner sampled header index body) := by
  unfold Goose.Lower.lowerEach
  apply (ReplacementSitesAt.eachLen _ _ _ _ _).bind
  apply (ReplacementSitesAt.emitDef _ (by intros; trivial)).bind
  have lengthGenerated : GeneratedBuilderState (Goose.Lower.eachLen regrow owner sampled le before).2 :=
    generated.eachLen regrow owner sampled rfl
  exact ReplacementSitesAt.loopBody_generated _ (lengthGenerated.emitDef _ rfl) bodyStorage
    (fun _ => ReplacementSitesAt.rangeBack _ _ _ _ _)

#print axioms ReplacementSitesAt.loopBody_generated
#print axioms ReplacementSitesAt.lowerWhile_generated
#print axioms ReplacementSitesAt.lowerRange_generated
#print axioms ReplacementSitesAt.lowerEach_generated

end Goose.Lower.Validation
