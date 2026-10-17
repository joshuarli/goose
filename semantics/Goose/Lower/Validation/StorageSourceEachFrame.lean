import Goose.Lower.Validation.StorageSourceHeaders

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem StorageAt.loopBody_withTypes {le : LEnv} {before : LS} (condition : ValueId)
    {body : Nat → BlockId → B ValueId} {back : B Unit}
    (generated : GeneratedBuilderState before)
    (bodyStorage : ∀ depth exit state, GeneratedBuilderState state → exit < state.blocks.size →
      before.blocks.size ≤ state.blocks.size → TypePrefix before state → StorageAt le state (body depth exit))
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
  have prefixTypes : TypePrefix before entered.2 :=
    (types_fork condition le before forked.1 forked.2 rfl).trans
      (types_setCur (some forked.1.1) le forked.2 entered.1 entered.2 rfl)
  unfold Goose.Lower.loopBody
  apply (StorageAt.get _ _).bind
  simp only [get_apply]
  apply (StorageAt.fork _ _ _).bind
  apply (StorageAt.setCur _ _ _).bind
  apply (bodyStorage before.stack.length forked.1.2 entered.2 enteredGenerated
    (by rw [entryBlocks]; exact exitBound) grows prefixTypes).bind
  exact (backStorage _).bind (StorageAt.setCur _ _ _)

theorem StorageAt.header_withTypes {le : LEnv} {before : LS} (types : List VTy) (arguments : List ValueId)
    {tail : BlockId → List ValueId → B α} (generated : GeneratedBuilderState before)
    (child : ∀ header parameters state, GeneratedBuilderState state → header < state.blocks.size →
      TypePrefix before state → StorageAt le state (tail header parameters)) :
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
  have prefixTypes : TypePrefix before entered.2 :=
    (types_newBlock types le before allocated.1 allocated.2 rfl).trans
      ((types_emitTerm (.br allocated.1.1 arguments) le allocated.2 closed.1 closed.2 rfl).trans
        (types_setCur (some allocated.1.1) le closed.2 entered.1 entered.2 rfl))
  apply (StorageAt.newBlock _ _ _).bind
  apply (StorageAt.emitTerm _ _ _).bind
  apply (StorageAt.setCur _ _ _).bind
  exact child allocated.1.1 allocated.1.2 entered.2 enteredGenerated laterBound prefixTypes

theorem StorageAt.header1_withTypes {le : LEnv} {before : LS} (type : VTy) (arguments : List ValueId)
    {tail : BlockId → ValueId → B α} (generated : GeneratedBuilderState before)
    (child : ∀ header parameter state, GeneratedBuilderState state → header < state.blocks.size →
      TypePrefix before state → state.vals[parameter]? = some (some type) → StorageAt le state (tail header parameter)) :
    StorageAt le before (do
      let (header, parameters) ← Goose.Lower.newBlock [type]
      Goose.Lower.emitTerm (.br header arguments)
      Goose.Lower.setCur (some header)
      tail header (parameters.headD 0)) := by
  let allocated := Goose.Lower.newBlock [type] le before
  let closed := Goose.Lower.emitTerm (.br allocated.1.1 arguments) le allocated.2
  let entered := Goose.Lower.setCur (some allocated.1.1) le closed.2
  have allocatedGenerated := generated.newBlock [type]
    (show Goose.Lower.newBlock [type] le before = allocated from rfl)
  have id : allocated.1.1 = before.blocks.size := by simp [allocated, newBlock1_run]
  have size : allocated.2.blocks.size = before.blocks.size + 1 := by simp [allocated, newBlock1_run]
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
  have suffixTypes : TypePrefix allocated.2 entered.2 :=
    (types_emitTerm (.br allocated.1.1 arguments) le allocated.2 closed.1 closed.2 rfl).trans
      (types_setCur (some allocated.1.1) le closed.2 entered.1 entered.2 rfl)
  have prefixTypes := (types_newBlock [type] le before allocated.1 allocated.2 rfl).trans suffixTypes
  have parameterTyped : allocated.2.vals[allocated.1.2.headD 0]? = some (some type) := by
    simp [allocated, newBlock1_run]
  apply (StorageAt.newBlock _ _ _).bind
  apply (StorageAt.emitTerm _ _ _).bind
  apply (StorageAt.setCur _ _ _).bind
  exact child allocated.1.1 (allocated.1.2.headD 0) entered.2 enteredGenerated laterBound prefixTypes
    (suffixTypes _ _ parameterTyped)

theorem StorageAt.lowerEach_withTypes {le : LEnv} {before : LS} (regrow : Bool) (owner : Option ValueId)
    (sampled : ValueId) (header : BlockId) (index : ValueId) {body : Nat → BlockId → B ValueId}
    (generated : GeneratedBuilderState before)
    (bodyStorage : ∀ depth exit state, GeneratedBuilderState state → exit < state.blocks.size →
      (Goose.Lower.emitDef (.cmp .lt .i64 index (Goose.Lower.eachLen regrow owner sampled le before).1)
        le (Goose.Lower.eachLen regrow owner sampled le before).2).2.blocks.size ≤ state.blocks.size →
      TypePrefix before state → StorageAt le state (body depth exit)) :
    StorageAt le before (Goose.Lower.lowerEach regrow owner sampled header index body) := by
  let length := Goose.Lower.eachLen regrow owner sampled le before
  let compared := Goose.Lower.emitDef (.cmp .lt .i64 index length.1) le length.2
  have lengthGenerated : GeneratedBuilderState length.2 := generated.eachLen regrow owner sampled rfl
  have prefixTypes : TypePrefix before compared.2 :=
    (types_eachLen regrow owner sampled le before length.1 length.2 rfl).trans
      (types_emitDef (.cmp .lt .i64 index length.1) le length.2 compared.1 compared.2 rfl)
  unfold Goose.Lower.lowerEach
  apply (StorageAt.eachLen _ _ _ _ _).bind
  apply (StorageAt.emitDef _ (by intros; trivial)).bind
  apply StorageAt.loopBody_withTypes _ (lengthGenerated.emitDef _ rfl)
  · intro depth exit state current exitBound grows frames
    exact bodyStorage depth exit state current exitBound grows (prefixTypes.trans frames)
  · exact fun _ => StorageAt.rangeBack _ _ _ _ _

end Goose.Lower.Validation
