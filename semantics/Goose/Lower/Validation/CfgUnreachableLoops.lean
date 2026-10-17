import Goose.Lower.Validation.CfgUnreachableControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem unreachable_rangeBack (ty : IntTy) (counter header : ValueId) :
    UnreachableRun (rangeBack ty counter header) := by
  unfold rangeBack
  refine UnreachableRun.bind unreachable_isLive fun live => ?_
  cases live
  · exact unreachable_pure _
  · exact UnreachableRun.bind (unreachable_emitDef _) fun _ =>
      unreachable_emitTerm _ (by intro h; cases h)

theorem unreachable_loopBody (condition : ValueId) {body : Nat → BlockId → B ValueId}
    {back : B Unit} (bodyChecked : ∀ depth exit, UnreachableRun (body depth exit))
    (backChecked : UnreachableRun back) : UnreachableRun (loopBody condition body back) := by
  unfold loopBody
  refine UnreachableRun.bind unreachable_get fun saved => ?_
  refine UnreachableRun.bind (unreachable_fork condition) fun pair => ?_
  refine UnreachableRun.bind (unreachable_setCur _) fun _ => ?_
  refine UnreachableRun.bind (bodyChecked _ _) fun _ => ?_
  exact UnreachableRun.bind backChecked fun _ => unreachable_setCur _

theorem unreachable_lowerWhile (header : BlockId) {condition : B ValueId}
    {body : Nat → BlockId → B ValueId} (conditionChecked : UnreachableRun condition)
    (bodyChecked : ∀ depth exit, UnreachableRun (body depth exit)) :
    UnreachableRun (lowerWhile header condition body) := by
  unfold lowerWhile
  refine UnreachableRun.bind conditionChecked fun value => ?_
  exact unreachable_whenLive _ fun _ => unreachable_loopBody value bodyChecked
    (unreachable_emitTerm _ (by intro h; cases h))

theorem unreachable_lowerRange (hint : IntTy) (counter bound header : ValueId)
    {body : Nat → BlockId → B ValueId} (bodyChecked : ∀ depth exit, UnreachableRun (body depth exit)) :
    UnreachableRun (lowerRange hint counter bound header body) := by
  unfold lowerRange
  exact UnreachableRun.bind (unreachable_emitDef _) fun value =>
    unreachable_loopBody value bodyChecked (unreachable_rangeBack hint counter header)

theorem unreachable_lowerEach (regrow : Bool) (owner : Option ValueId)
    (sampled header counter : ValueId) {body : Nat → BlockId → B ValueId}
    (bodyChecked : ∀ depth exit, UnreachableRun (body depth exit)) :
    UnreachableRun (lowerEach regrow owner sampled header counter body) := by
  unfold lowerEach
  refine UnreachableRun.bind (unreachable_eachLen _ _ _) fun length => ?_
  exact UnreachableRun.bind (unreachable_emitDef _) fun condition =>
    unreachable_loopBody condition bodyChecked (unreachable_rangeBack .i64 counter header)

theorem unreachable_header0 {tail : BlockId → B Unit}
    (checked : ∀ header, UnreachableRun (tail header)) :
    UnreachableRun (do
      let (header, _) ← newBlock []
      emitTerm (.br header [])
      setCur (some header)
      tail header) := by
  refine UnreachableRun.bind (unreachable_newBlock []) fun pair => ?_
  refine UnreachableRun.bind (unreachable_emitTerm _ (by intro h; cases h)) fun _ => ?_
  exact UnreachableRun.bind (unreachable_setCur _) fun _ => checked _

theorem unreachable_header1 (ty : VTy) (initial : ValueId)
    {tail : BlockId → ValueId → B Unit} (checked : ∀ header counter, UnreachableRun (tail header counter)) :
    UnreachableRun (do
      let (header, ids) ← newBlock [ty]
      let counter := ids.headD 0
      emitTerm (.br header [initial])
      setCur (some header)
      tail header counter) := by
  refine UnreachableRun.bind (unreachable_newBlock [ty]) fun pair => ?_
  refine UnreachableRun.bind (unreachable_emitTerm _ (by intro h; cases h)) fun _ => ?_
  exact UnreachableRun.bind (unreachable_setCur _) fun _ => checked _ _

end Goose.Lower.Validation
