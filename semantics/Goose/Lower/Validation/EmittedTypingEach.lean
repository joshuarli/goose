import Goose.Lower.Validation.EmittedTypingLoops

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def EmittedEachLengthTypes (state : LS) (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) : Prop :=
  if regrow then ∃ mu ownerType element,
    state.vals[owner.getD 0]? = some (some (.data (.ref mu ownerType))) ∧ arrayElem? ownerType = some element
  else state.vals[sampled]? = some (some (.data (.int .i64)))

theorem EmittedEachLengthTypes.retained {before after : LS} {regrow : Bool} {owner : Option ValueId} {sampled : ValueId}
    (typed : EmittedEachLengthTypes before regrow owner sampled) (retained : TypePrefix before after) :
    EmittedEachLengthTypes after regrow owner sampled := by
  cases regrow
  · exact retained sampled (.data (.int .i64)) typed
  · obtain ⟨mu, ownerType, element, row, array⟩ := typed
    exact ⟨mu, ownerType, element, retained _ _ row, array⟩

theorem emitted_checked_eachLen {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (regrow : Bool) (owner : Option ValueId) (sampled : ValueId)
    (typed : EmittedEachLengthTypes before regrow owner sampled) :
    let result := Goose.Lower.eachLen regrow owner sampled le before
    EmittedBuilder le initial result.2 ∧ (result.2.cur.isSome = true → result.2.vals[result.1]? = some (some (.data (.int .i64)))) := by
  cases regrow
  · exact ⟨builder, fun _ => typed⟩
  · obtain ⟨mu, ownerType, element, row, array⟩ := typed
    have success : (Op.arrayLen (owner.getD 0)).resultTy (tyEnv le before) = .ok (.data (.int .i64)) := by
      simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, row, array,
        pure, Except.pure, bind, Except.bind]
    have emitted := builder.emitDef (.arrayLen (owner.getD 0)) (fun _ => ⟨.data (.int .i64), success⟩) (by
      intro active operand member
      have same : operand = owner.getD 0 := by simpa [Op.uses] using member
      subst operand
      exact (Array.getElem?_eq_some_iff.mp row).1)
    refine ⟨emitted, ?_⟩
    intro active
    cases current : before.cur with
    | none =>
      have dead := emitDef_none (.arrayLen (owner.getD 0)) le current
      simp only [Goose.Lower.eachLen, reduceIte, dead, current, Option.isSome_none] at active
      cases active
    | some block => exact (emitDef_recorded current success).2.2.1

theorem emitted_checked_lowerEach {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (regrow : Bool) (owner : Option ValueId) (sampled header counter : ValueId)
    {current : BlockId} (live : before.cur = some current)
    (counterTyped : before.vals[counter]? = some (some (.data (.int .i64))))
    (lengthTyped : EmittedEachLengthTypes before regrow owner sampled)
    (body : Nat → BlockId → B ValueId)
    (bodyChecked : ∀ depth target initial started, EmittedBuilder le initial started →
      started.vals[counter]? = some (some (.data (.int .i64))) → TypePrefix before started →
      EmittedBuilder le initial (body depth target le started).2)
    (bodyAdvance : ∀ depth target, AdvB (body depth target))
    (bodyTypes : ∀ depth target, TypeRun (body depth target)) :
    EmittedBuilder le initial (Goose.Lower.lowerEach regrow owner sampled header counter body le before).2 := by
  let length := Goose.Lower.eachLen regrow owner sampled le before
  have lengthProof := emitted_checked_eachLen builder regrow owner sampled lengthTyped
  have lengthLive : length.2.cur = some current := by
    cases regrow
    · exact live
    · cases source : before.cur with
      | none => rw [live] at source; cases source
      | some block =>
        simp only [length, Goose.Lower.eachLen, reduceIte, emitDef_run _ _ source]
        exact live
  have lengthRow := lengthProof.2 (by rw [lengthLive]; rfl)
  have retainedCounter := (types_eachLen regrow owner sampled le before _ _ rfl) counter (.data (.int .i64)) counterTyped
  have output := emitted_checked_lowerRange lengthProof.1 header .i64 counter length.1 lengthLive
    retainedCounter lengthRow body
    (fun depth target initial started builder counter prefixProof => bodyChecked depth target initial started builder counter
      ((types_eachLen regrow owner sampled le before _ _ rfl).trans prefixProof))
    bodyAdvance bodyTypes
  exact output

end Goose.Lower.Validation
