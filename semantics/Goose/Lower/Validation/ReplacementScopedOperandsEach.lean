import Goose.Lower.Validation.ReplacementScopedOperandsLiveBlocks

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem rhs_regrowOf_state (owner : Option ValueId) (env : LEnv) (before : LS) :
    (regrowOf owner env before).2 = before := by
  cases owner with
  | none => rfl
  | some address =>
    simp only [regrowOf, growOwner, bind_run]
    have same := valTy_run address env before
    cases evaluated : valTy address env before with
    | mk type after =>
      simp only [evaluated] at same ⊢
      cases type with
      | data type => cases type <;> exact same
      | view _ _ => exact same

theorem rhs_regrowOf_dead (owner : Option ValueId) : DeadRun (regrowOf owner) := by
  intro env before result after run dead
  have same := rhs_regrowOf_state owner env before
  rw [run] at same
  have equal : after = before := same
  rw [equal]
  exact dead

theorem rhs_regrowOf_hasOwner {owner : Option ValueId} {env : LEnv} {before after : LS}
    (run : regrowOf owner env before = (true, after)) : owner.isSome = true := by
  cases owner with
  | none => have equal := congrArg Prod.fst run; cases equal
  | some _ => rfl

theorem rhs_eachSampled_dead (regrow : Bool) (view : ValueId) : DeadRun (eachSampled regrow view) := by
  cases regrow
  · exact dead_emitDef _
  · exact DeadRun.pure _

theorem rhs_eachSource_fresh (floor : Nat) (view : View) {env before owner value after}
    (bound : floor ≤ before.vals.size)
    (run : lowerEachSource view env before = ((owner, value), after)) (live : after.cur.isSome = true) :
    (∀ address, owner = some address → floor ≤ address) ∧ floor ≤ value := by
  cases view with
  | of place =>
    simp only [lowerEachSource, bind_eq] at run
    obtain ⟨address, addressed, addressRun, sampled, ended, sampleRun, final⟩ := run
    obtain ⟨pair, rfl⟩ := pure_eq.mp final
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
    have addressFresh := RhsValueFresh.output bound (freshValue_lowerPlace place) addressRun
    have addressLive := live_before (dead_emitDef _) sampleRun live
    exact ⟨fun other equal => Option.some.inj equal ▸ addressFresh addressLive,
      Nat.le_trans bound (Nat.le_trans (advB_lowerPlace place env before address addressed addressRun).vals
        (freshValue_emitDef _ env addressed sampled ended sampleRun live))⟩
  | val expression =>
    simp only [lowerEachSource, bind_eq] at run
    obtain ⟨slice, sliced, sliceRun, sampled, ended, sampleRun, final⟩ := run
    obtain ⟨pair, rfl⟩ := pure_eq.mp final
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
    constructor
    · intro address equal
      cases equal
    · exact Nat.le_trans bound (Nat.le_trans (advB_lowerExpr expression env before slice sliced sliceRun).vals
      (freshValue_emitDef _ env sliced sampled ended sampleRun live))

theorem rhsOperands_eachSampled (floor : Nat) (env : LEnv) (before : LS) (regrow : Bool)
    (view : ValueId) (fresh : RhsValueFresh floor before view) :
    RhsOperandsAt floor env before (eachSampled regrow view) := by
  cases regrow
  · exact RhsOperandsAt.emitDef _ _ _ _ (by simpa only [Op.uses, List.mem_singleton] using
      fun live value equal => equal ▸ (fresh live))
  · exact RhsOperandsAt.pure _ _ _ _

theorem rhsOperands_lowerEach (floor : Nat) (regrow : Bool) (owner : Option ValueId)
    (sampled : ValueId) (header : BlockId) (counter : ValueId) (body : Nat → BlockId → B ValueId)
    (ownerFresh : regrow = true → floor ≤ owner.getD 0)
    (sampledFresh : regrow = false → floor ≤ sampled) (counterFresh : floor ≤ counter)
    (bodyAdvance : ∀ depth exit, AdvB (body depth exit))
    (bodyChild : ∀ depth exit, RhsOperandsRun floor (body depth exit)) :
    RhsOperandsRun floor (lowerEach regrow owner sampled header counter body) := by
  intro env before bound
  let measured := eachLen regrow owner sampled env before
  have measuredFresh : RhsValueFresh floor measured.2 measured.1 := by
    cases regrow
    · exact fun _ => sampledFresh rfl
    · exact RhsValueFresh.output bound (freshValue_emitDef _) rfl
  have measuredBound : floor ≤ measured.2.vals.size :=
    Nat.le_trans bound (advB_eachLen regrow owner sampled env before measured.1 measured.2 rfl).vals
  unfold lowerEach
  apply RhsOperandsAt.bind
    (first := eachLen regrow owner sampled)
  · cases regrow
    · exact RhsOperandsAt.pure _ _ _ _
    · exact RhsOperandsAt.emitDef _ _ _ _ (by simp [Op.uses, ownerFresh rfl])
  · apply RhsOperandsAt.bindFresh measuredBound
      (RhsOperandsAt.emitDef floor env measured.2 (.cmp .lt .i64 counter measured.1) ?_)
      (advB_emitDef _) (freshValue_emitDef _)
    · intro condition compared _ comparedBound conditionFresh
      exact rhsOperands_loopBody floor condition body (rangeBack .i64 counter header) bodyAdvance bodyChild
        (rhsOperands_rangeBack floor .i64 counter header counterFresh)
        env compared comparedBound conditionFresh
    · intro live value member
      simp only [Op.uses, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact counterFresh
      · exact measuredFresh live

end Goose.Lower.Validation
