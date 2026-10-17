import Goose.Lower.Validation.SummaryPreservationReturnLedgerControlActions

namespace Goose.Lower.Validation.SummaryPreservation.ReturnLedgerControl

open Goose.Core Goose.GIR

def conditionPrefix (condition : B ValueId) : B (Nat × BlockId) := do
  let value ← condition
  loopPrefix value

theorem lowerWhile_origin {header : BlockId} {condition : B ValueId}
    {body : Nat → BlockId → B ValueId} {env : LEnv} {initial final : LS}
    {result : Unit} {values : List ValueId} {origin : Option OriginId}
    (conditionFrame : ReturnFrameRun condition)
    (run : lowerWhile header condition body env initial = (result, final))
    (member : .term (.ret values origin) ∈ final.insts) :
    .term (.ret values origin) ∈ initial.insts ∨
      Nonempty (ReturnCheckpoint (conditionPrefix condition) (fun pair => body pair.1 pair.2) env initial values origin) := by
  obtain ⟨value, middle, conditionRun, tail⟩ := bind_eq.mp run
  cases current : middle.cur with
  | none =>
    rw [whenLive_none _ _ _ current] at tail
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj tail
    exact Or.inl (conditionFrame env initial value middle conditionRun values origin member)
  | some block =>
    rw [whenLive_some _ _ _ current] at tail
    obtain ⟨checkpoint⟩ := loopBody_origin
      (frame _ (fun _ => ReturnFrames.returnAbsent_emitTerm _ (by intro _ _ same; cases same))) tail member
    refine Or.inr ⟨⟨checkpoint.argument, checkpoint.before, checkpoint.value, checkpoint.after, ?_, checkpoint.childRun, checkpoint.member⟩⟩
    simpa only [conditionPrefix, bind_run, conditionRun] using checkpoint.prefixRun

theorem prefixed_loop_origin {condition : B ValueId} {body : Nat → BlockId → B ValueId}
    {back : B Unit} {env : LEnv} {initial final : LS} {result : Unit}
    {values : List ValueId} {origin : Option OriginId}
    (backFrame : ReturnFrameRun back)
    (run : (do let value ← condition; loopBody value body back) env initial = (result, final))
    (member : .term (.ret values origin) ∈ final.insts) :
    Nonempty (ReturnCheckpoint (conditionPrefix condition) (fun pair => body pair.1 pair.2) env initial values origin) := by
  obtain ⟨value, middle, conditionRun, tail⟩ := bind_eq.mp run
  obtain ⟨checkpoint⟩ := loopBody_origin backFrame tail member
  refine ⟨⟨checkpoint.argument, checkpoint.before, checkpoint.value, checkpoint.after, ?_, checkpoint.childRun, checkpoint.member⟩⟩
  simpa only [conditionPrefix, bind_run, conditionRun] using checkpoint.prefixRun

theorem lowerRange_origin {hint : IntTy} {counter bound header : ValueId}
    {body : Nat → BlockId → B ValueId} {env : LEnv} {initial final : LS}
    {result : Unit} {values : List ValueId} {origin : Option OriginId}
    (run : lowerRange hint counter bound header body env initial = (result, final))
    (member : .term (.ret values origin) ∈ final.insts) :
    Nonempty (ReturnCheckpoint (conditionPrefix (emitDef (.cmp .lt hint counter bound)))
      (fun pair => body pair.1 pair.2) env initial values origin) :=
  prefixed_loop_origin (frame _ (fun _ => ReturnFrames.returnAbsent_rangeBack hint counter header)) run member

theorem lowerEach_origin {regrow : Bool} {owner : Option ValueId} {sampled header counter : ValueId}
    {body : Nat → BlockId → B ValueId} {env : LEnv} {initial final : LS}
    {result : Unit} {values : List ValueId} {origin : Option OriginId}
    (run : lowerEach regrow owner sampled header counter body env initial = (result, final))
    (member : .term (.ret values origin) ∈ final.insts) :
    Nonempty (ReturnCheckpoint
      (conditionPrefix (do let length ← eachLen regrow owner sampled; emitDef (.cmp .lt .i64 counter length)))
      (fun pair => body pair.1 pair.2) env initial values origin) := by
  exact prefixed_loop_origin
    (condition := do let length ← eachLen regrow owner sampled; emitDef (.cmp .lt .i64 counter length))
    (body := body) (back := rangeBack .i64 counter header)
    (frame _ (fun _ => ReturnFrames.returnAbsent_rangeBack .i64 counter header))
    (by simpa only [lowerEach, bind_run] using run) member

end Goose.Lower.Validation.SummaryPreservation.ReturnLedgerControl
