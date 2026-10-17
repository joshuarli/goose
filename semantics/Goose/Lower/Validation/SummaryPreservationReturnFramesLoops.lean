import Goose.Lower.Validation.SummaryPreservationReturnFramesControl

namespace Goose.Lower.Validation.SummaryPreservation.ReturnFrames

open Goose.Core Goose.GIR

variable {avoid : List ValueId × Option OriginId}

theorem returnAbsent_rangeBack (ty : IntTy) (counter header : ValueId) :
    ReturnAbsentRun (avoid := avoid) (rangeBack ty counter header) := by
  unfold rangeBack
  refine ReturnAbsentRun.bind returnAbsent_isLive fun live => ?_
  cases live
  · exact returnAbsent_pure _
  · exact ReturnAbsentRun.bind (returnAbsent_emitDef _) fun _ =>
      returnAbsent_emitTerm _ (by intro values origin h; cases h)

theorem returnAbsent_loopBody (condition : ValueId) {body : Nat → BlockId → B ValueId}
    {back : B Unit} (bodyChecked : ∀ depth exit, ReturnAbsentRun (avoid := avoid) (body depth exit))
    (backChecked : ReturnAbsentRun (avoid := avoid) back) : ReturnAbsentRun (avoid := avoid) (loopBody condition body back) := by
  unfold loopBody
  refine ReturnAbsentRun.bind returnAbsent_get fun saved => ?_
  refine ReturnAbsentRun.bind (returnAbsent_fork condition) fun pair => ?_
  refine ReturnAbsentRun.bind (returnAbsent_setCur _) fun _ => ?_
  refine ReturnAbsentRun.bind (bodyChecked _ _) fun _ => ?_
  exact ReturnAbsentRun.bind backChecked fun _ => returnAbsent_setCur _

theorem returnAbsent_lowerWhile (header : BlockId) {condition : B ValueId}
    {body : Nat → BlockId → B ValueId} (conditionChecked : ReturnAbsentRun (avoid := avoid) condition)
    (bodyChecked : ∀ depth exit, ReturnAbsentRun (avoid := avoid) (body depth exit)) :
    ReturnAbsentRun (avoid := avoid) (lowerWhile header condition body) := by
  unfold lowerWhile
  refine ReturnAbsentRun.bind conditionChecked fun value => ?_
  exact returnAbsent_whenLive _ fun _ => returnAbsent_loopBody value bodyChecked
    (returnAbsent_emitTerm _ (by intro values origin h; cases h))

theorem returnAbsent_lowerRange (hint : IntTy) (counter bound header : ValueId)
    {body : Nat → BlockId → B ValueId} (bodyChecked : ∀ depth exit, ReturnAbsentRun (avoid := avoid) (body depth exit)) :
    ReturnAbsentRun (avoid := avoid) (lowerRange hint counter bound header body) := by
  unfold lowerRange
  exact ReturnAbsentRun.bind (returnAbsent_emitDef _) fun value =>
    returnAbsent_loopBody value bodyChecked (returnAbsent_rangeBack hint counter header)

theorem returnAbsent_lowerEach (regrow : Bool) (owner : Option ValueId)
    (sampled header counter : ValueId) {body : Nat → BlockId → B ValueId}
    (bodyChecked : ∀ depth exit, ReturnAbsentRun (avoid := avoid) (body depth exit)) :
    ReturnAbsentRun (avoid := avoid) (lowerEach regrow owner sampled header counter body) := by
  unfold lowerEach
  refine ReturnAbsentRun.bind (returnAbsent_eachLen _ _ _) fun length => ?_
  exact ReturnAbsentRun.bind (returnAbsent_emitDef _) fun condition =>
    returnAbsent_loopBody condition bodyChecked (returnAbsent_rangeBack .i64 counter header)

theorem returnAbsent_header0 {tail : BlockId → B Unit}
    (checked : ∀ header, ReturnAbsentRun (avoid := avoid) (tail header)) :
    ReturnAbsentRun (avoid := avoid) (do
      let (header, _) ← newBlock []
      emitTerm (.br header [])
      setCur (some header)
      tail header) := by
  refine ReturnAbsentRun.bind (returnAbsent_newBlock []) fun pair => ?_
  refine ReturnAbsentRun.bind (returnAbsent_emitTerm _ (by intro values origin h; cases h)) fun _ => ?_
  exact ReturnAbsentRun.bind (returnAbsent_setCur _) fun _ => checked _

theorem returnAbsent_header1 (ty : VTy) (initial : ValueId)
    {tail : BlockId → ValueId → B Unit} (checked : ∀ header counter, ReturnAbsentRun (avoid := avoid) (tail header counter)) :
    ReturnAbsentRun (avoid := avoid) (do
      let (header, ids) ← newBlock [ty]
      let counter := ids.headD 0
      emitTerm (.br header [initial])
      setCur (some header)
      tail header counter) := by
  refine ReturnAbsentRun.bind (returnAbsent_newBlock [ty]) fun pair => ?_
  refine ReturnAbsentRun.bind (returnAbsent_emitTerm _ (by intro values origin h; cases h)) fun _ => ?_
  exact ReturnAbsentRun.bind (returnAbsent_setCur _) fun _ => checked _ _

end Goose.Lower.Validation.SummaryPreservation.ReturnFrames
