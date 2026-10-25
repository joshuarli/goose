import Goose.Lower.Validation.ReplacementScopedOperandsExpressions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem RhsOperandsAt.scFork (floor : Nat) (env : LEnv) (before : LS)
    (isAnd : Bool) (condition : ValueId) (fresh : RhsValueFresh floor before condition) :
    RhsOperandsAt floor env before (Goose.Lower.scFork isAnd condition) := by
  unfold Goose.Lower.scFork
  apply (RhsOperandsAt.newBlock _ _ _ _).bindRun
  intro right rightState rightRun
  apply (RhsOperandsAt.newBlock _ _ _ _).bindRun
  intro join joinState joinRun
  have rightCurrent : rightState.cur = before.cur := by
    have projected := congrArg (fun pair => pair.2.cur) rightRun
    simpa only [newBlock0_run] using projected.symm
  have joinCurrent : joinState.cur = rightState.cur := by
    have projected := congrArg (fun pair => pair.2.cur) joinRun
    simpa only [newBlock1_run] using projected.symm
  apply RhsOperandsAt.bindRun
    (next := fun _ => (Pure.pure (right.1, join.1, join.2.headD 0) : B _))
  · cases isAnd <;> apply RhsOperandsAt.emitTerm <;>
      intro live value member <;>
      have equal : value = condition := by simpa [Term.uses] using member
    all_goals subst value; exact fresh (by simpa only [joinCurrent, rightCurrent] using live)
  · intro _ _ _
    exact RhsOperandsAt.pure _ _ _ _

theorem rhsOperands_shortCircuit (floor : Nat) (isAnd : Bool) (condition : ValueId)
    {rhs : B ValueId} (_advance : AdvB rhs) (fresh : FreshValueRun rhs)
    (child : RhsOperandsRun floor rhs) (env : LEnv) (before : LS)
    (bound : floor ≤ before.vals.size) (conditionFresh : RhsValueFresh floor before condition) :
    RhsOperandsAt floor env before (shortCircuit isAnd condition rhs) := by
  let forked := Goose.Lower.scFork isAnd condition env before
  let entered := Goose.Lower.setCur (some forked.1.1) env forked.2
  let ended := rhs env entered.2
  have enteredBound : floor ≤ entered.2.vals.size :=
    Nat.le_trans bound (advB_scFork isAnd condition env before forked.1 forked.2 rfl).vals
  have valueFresh := RhsValueFresh.output enteredBound fresh (rfl : rhs env entered.2 = ended)
  unfold shortCircuit
  apply RhsOperandsAt.whenLive
  intro block live
  apply (RhsOperandsAt.scFork floor env before isAnd condition conditionFresh).bind
  apply (RhsOperandsAt.setCur _ _ _ _).bind
  apply (child env entered.2 enteredBound).bind
  apply (RhsOperandsAt.emitTerm floor env ended.2 (.br forked.1.2.1 [ended.1]) ?_).bind
  · exact (RhsOperandsAt.setCur _ _ _ _).bind (RhsOperandsAt.pure _ _ _ _)
  · simpa only [Term.uses, List.mem_singleton] using
      fun live value equal => equal ▸ valueFresh live

theorem rhsOperands_forkActions (floor : Nat) (env : LEnv) (before : LS)
    (condition : ValueId) {first second : B ValueId}
    (bound : floor ≤ before.vals.size) (conditionFresh : RhsValueFresh floor before condition)
    (advance : AdvB first) (freshFirst : FreshValueRun first) (freshSecond : FreshValueRun second)
    (one : RhsOperandsRun floor first) (two : RhsOperandsRun floor second) :
    RhsOperandsAt floor env before (do
      let (yes, no) ← fork condition
      setCur (some yes)
      let yesValue ← first
      let yesEnd ← curBlock
      setCur (some no)
      let noValue ← second
      let noEnd ← curBlock
      joinValue yesEnd yesValue noEnd noValue) := by
  let forked := Goose.Lower.fork condition env before
  let enteredYes := Goose.Lower.setCur (some forked.1.1) env forked.2
  let endedYes := first env enteredYes.2
  let enteredNo := Goose.Lower.setCur (some forked.1.2) env endedYes.2
  let endedNo := second env enteredNo.2
  have yesBound : floor ≤ enteredYes.2.vals.size :=
    Nat.le_trans bound (advB_fork condition env before forked.1 forked.2 rfl).vals
  have noBound : floor ≤ enteredNo.2.vals.size :=
    Nat.le_trans yesBound (advance env enteredYes.2 endedYes.1 endedYes.2 rfl).vals
  have yesFresh := RhsValueFresh.output yesBound freshFirst (rfl : first env enteredYes.2 = endedYes)
  have noFresh := RhsValueFresh.output noBound freshSecond (rfl : second env enteredNo.2 = endedNo)
  apply (RhsOperandsAt.fork floor env before condition conditionFresh).bind
  apply (RhsOperandsAt.setCur _ _ _ _).bind
  apply (one env enteredYes.2 yesBound).bind
  apply (RhsOperandsAt.curBlock _ _ _).bind
  simp only [curBlock_run]
  apply (RhsOperandsAt.setCur _ _ _ _).bind
  apply (two env enteredNo.2 noBound).bind
  apply (RhsOperandsAt.curBlock _ _ _).bind
  simp only [curBlock_run]
  exact RhsOperandsAt.joinValue floor env endedNo.2 endedYes.2.cur endedNo.2.cur
    endedYes.1 endedNo.1 yesFresh noFresh

end Goose.Lower.Validation
