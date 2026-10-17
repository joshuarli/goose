import Goose.Lower.Validation.CfgReturnFreeControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem returnFree_rangeBack (ty : IntTy) (counter header : ValueId) :
    ReturnFreeRun (rangeBack ty counter header) := by
  unfold rangeBack
  refine ReturnFreeRun.bind returnFree_isLive fun live => ?_
  cases live
  · exact returnFree_pure _
  · exact ReturnFreeRun.bind (returnFree_emitDef _) fun _ =>
      returnFree_emitTerm _ (by intro values origin h; cases h)

theorem returnFree_loopBody (condition : ValueId) {body : Nat → BlockId → B ValueId}
    {back : B Unit} (bodyChecked : ∀ depth exit, ReturnFreeRun (body depth exit))
    (backChecked : ReturnFreeRun back) : ReturnFreeRun (loopBody condition body back) := by
  unfold loopBody
  refine ReturnFreeRun.bind returnFree_get fun saved => ?_
  refine ReturnFreeRun.bind (returnFree_fork condition) fun pair => ?_
  refine ReturnFreeRun.bind (returnFree_setCur _) fun _ => ?_
  refine ReturnFreeRun.bind (bodyChecked _ _) fun _ => ?_
  exact ReturnFreeRun.bind backChecked fun _ => returnFree_setCur _

theorem returnFree_lowerWhile (header : BlockId) {condition : B ValueId}
    {body : Nat → BlockId → B ValueId} (conditionChecked : ReturnFreeRun condition)
    (bodyChecked : ∀ depth exit, ReturnFreeRun (body depth exit)) :
    ReturnFreeRun (lowerWhile header condition body) := by
  unfold lowerWhile
  refine ReturnFreeRun.bind conditionChecked fun value => ?_
  exact returnFree_whenLive _ fun _ => returnFree_loopBody value bodyChecked
    (returnFree_emitTerm _ (by intro values origin h; cases h))

theorem returnFree_lowerRange (hint : IntTy) (counter bound header : ValueId)
    {body : Nat → BlockId → B ValueId} (bodyChecked : ∀ depth exit, ReturnFreeRun (body depth exit)) :
    ReturnFreeRun (lowerRange hint counter bound header body) := by
  unfold lowerRange
  exact ReturnFreeRun.bind (returnFree_emitDef _) fun value =>
    returnFree_loopBody value bodyChecked (returnFree_rangeBack hint counter header)

theorem returnFree_lowerEach (regrow : Bool) (owner : Option ValueId)
    (sampled header counter : ValueId) {body : Nat → BlockId → B ValueId}
    (bodyChecked : ∀ depth exit, ReturnFreeRun (body depth exit)) :
    ReturnFreeRun (lowerEach regrow owner sampled header counter body) := by
  unfold lowerEach
  refine ReturnFreeRun.bind (returnFree_eachLen _ _ _) fun length => ?_
  exact ReturnFreeRun.bind (returnFree_emitDef _) fun condition =>
    returnFree_loopBody condition bodyChecked (returnFree_rangeBack .i64 counter header)

theorem returnFree_header0 {tail : BlockId → B Unit}
    (checked : ∀ header, ReturnFreeRun (tail header)) :
    ReturnFreeRun (do
      let (header, _) ← newBlock []
      emitTerm (.br header [])
      setCur (some header)
      tail header) := by
  refine ReturnFreeRun.bind (returnFree_newBlock []) fun pair => ?_
  refine ReturnFreeRun.bind (returnFree_emitTerm _ (by intro values origin h; cases h)) fun _ => ?_
  exact ReturnFreeRun.bind (returnFree_setCur _) fun _ => checked _

theorem returnFree_header1 (ty : VTy) (initial : ValueId)
    {tail : BlockId → ValueId → B Unit} (checked : ∀ header counter, ReturnFreeRun (tail header counter)) :
    ReturnFreeRun (do
      let (header, ids) ← newBlock [ty]
      let counter := ids.headD 0
      emitTerm (.br header [initial])
      setCur (some header)
      tail header counter) := by
  refine ReturnFreeRun.bind (returnFree_newBlock [ty]) fun pair => ?_
  refine ReturnFreeRun.bind (returnFree_emitTerm _ (by intro values origin h; cases h)) fun _ => ?_
  exact ReturnFreeRun.bind (returnFree_setCur _) fun _ => checked _ _

end Goose.Lower.Validation
