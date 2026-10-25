import Goose.Lower.Validation.ReplacementScopedOperandsEachStatement

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem rhsOperands_ifStatement (floor : Nat) (loop : Option LoopCtx) (condition : Expr)
    (yes : Core.Block) (no : Option Core.Block) (origin : OriginId)
    (loopFresh : RhsLoopFresh floor loop)
    (conditionChild : RhsOperandsRun floor (lowerExpr condition))
    (yesChild : RhsBlockChild floor yes) (noChild : ∀ block, no = some block → RhsBlockChild floor block) :
    RhsOperandsRun floor (lowerStmt loop (.ifS condition yes no origin)) := by
  cases no with
  | none =>
    intro env before bound
    simp only [lowerStmt]
    apply RhsOperandsAt.bindFresh bound (conditionChild env before bound)
      (advB_lowerExpr condition) (freshValue_lowerExpr condition)
    intro value tested _ testedBound valueFresh
    apply RhsOperandsAt.whenLive
    intro block active
    let forked := fork value env tested
    let enteredYes := setCur (some forked.1.1) env forked.2
    let endedYes := lowerBlock loop [] false yes env enteredYes.2
    have yesBound : floor ≤ enteredYes.2.vals.size :=
      Nat.le_trans testedBound (advB_fork value env tested forked.1 forked.2 rfl).vals
    have endedYesBound : floor ≤ endedYes.2.vals.size := Nat.le_trans yesBound
      (advB_lowerBlock loop [] false yes env enteredYes.2 endedYes.1 endedYes.2 rfl).vals
    apply (RhsOperandsAt.fork _ _ _ _ valueFresh).bind
    apply (RhsOperandsAt.setCur _ _ _ _).bind
    apply (yesChild _ _ _ _ _ yesBound loopFresh (by simp [RhsPreFresh])).bind
    exact (RhsOperandsAt.emitTerm _ _ _ _ (by simp [Term.uses])).bind (RhsOperandsAt.setCur _ _ _ _)
  | some no =>
    intro env before bound
    simp only [lowerStmt]
    apply RhsOperandsAt.bindFresh bound (conditionChild env before bound)
      (advB_lowerExpr condition) (freshValue_lowerExpr condition)
    intro value tested _ testedBound valueFresh
    apply RhsOperandsAt.whenLive
    intro block active
    let forked := fork value env tested
    let enteredYes := setCur (some forked.1.1) env forked.2
    let endedYes := lowerBlock loop [] false yes env enteredYes.2
    have yesBound : floor ≤ enteredYes.2.vals.size :=
      Nat.le_trans testedBound (advB_fork value env tested forked.1 forked.2 rfl).vals
    have endedYesBound : floor ≤ endedYes.2.vals.size := Nat.le_trans yesBound
      (advB_lowerBlock loop [] false yes env enteredYes.2 endedYes.1 endedYes.2 rfl).vals
    let enteredNo := setCur (some forked.1.2) env endedYes.2
    apply (RhsOperandsAt.fork _ _ _ _ valueFresh).bind
    apply (RhsOperandsAt.setCur _ _ _ _).bind
    apply (yesChild _ _ _ _ _ yesBound loopFresh (by simp [RhsPreFresh])).bind
    apply (RhsOperandsAt.curBlock _ _ _).bind
    simp only [curBlock_run]
    apply (RhsOperandsAt.setCur _ _ _ _).bind
    apply (noChild no rfl _ _ _ _ enteredNo.2 endedYesBound loopFresh (by simp [RhsPreFresh])).bind
    apply (RhsOperandsAt.curBlock _ _ _).bind
    simp only [curBlock_run]
    exact RhsOperandsAt.joinArms _ _ _ _ _

theorem rhsOperands_assertStatement (floor : Nat) (loop : Option LoopCtx)
    (condition : Expr) (origin : OriginId)
    (child : RhsOperandsRun floor (lowerExpr condition)) :
    RhsOperandsRun floor (lowerStmt loop (.assertS condition origin)) := by
  intro env before bound
  simp only [lowerStmt]
  apply RhsOperandsAt.bindFresh bound (child env before bound)
    (advB_lowerExpr condition) (freshValue_lowerExpr condition)
  intro value tested _ _ valueFresh
  apply RhsOperandsAt.whenLive
  intro block active
  apply (RhsOperandsAt.fork _ _ _ _ valueFresh).bind
  apply (RhsOperandsAt.setCur _ _ _ _).bind
  exact (RhsOperandsAt.emitTerm _ _ _ _ (by simp [Term.uses])).bind (RhsOperandsAt.setCur _ _ _ _)

theorem rhsOperands_ifExpression (floor : Nat) (condition : Expr) (yes no : Core.Block)
    (conditionChild : RhsOperandsRun floor (lowerExpr condition))
    (yesChild : RhsBlockChild floor yes) (noChild : RhsBlockChild floor no) :
    RhsOperandsRun floor (lowerExpr (.ifE condition yes no)) := by
  intro env before bound
  simp only [lowerExpr]
  apply RhsOperandsAt.bindFresh bound (conditionChild env before bound)
    (advB_lowerExpr condition) (freshValue_lowerExpr condition)
  intro value tested _ testedBound valueFresh
  apply RhsOperandsAt.whenLive
  intro block active
  have branches := rhsOperands_forkActions floor env tested value testedBound valueFresh
    (advB_lowerBlock none [] true yes) (freshValue_lowerBlock none [] yes) (freshValue_lowerBlock none [] no)
    (fun env state bound => yesChild none [] true env state bound trivial (by simp [RhsPreFresh]))
    (fun env state bound => noChild none [] true env state bound trivial (by simp [RhsPreFresh]))
  simp only [RhsOperandsAt, bind_run] at branches ⊢
  cases forkRun : fork value env tested with
  | mk pair forkState =>
    cases pair with
    | mk yesBlock noBlock =>
      simp only [forkRun] at branches ⊢
      apply branches.trans
      apply EmitsOnly.of_blocks
      exact (recordValueRootRecipe_run _ _ _ _ ▸ rfl)


end Goose.Lower.Validation
