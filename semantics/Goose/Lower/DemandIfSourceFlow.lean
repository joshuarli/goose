import Goose.Lower.DemandIfBranchOccurrence

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Fuel

theorem if_then_source_success {cfg : Cfg} {env : Env} {condition : Expr} {yes : Core.Block}
    {no : Option Core.Block} {origin : OriginId} {state middle after : St} {conditionFuel branchFuel : Nat}
    (conditionDone : evalExpr conditionFuel cfg env condition state = .ok (.bool true) middle)
    (branchDone : execBlock branchFuel cfg env [] yes middle = .ok (.normal .unit) after) :
    ∃ fuel, execStmt fuel cfg env (.ifS condition yes no origin) state = .ok (.normal .unit) after := by
  let common := max conditionFuel branchFuel
  have conditionAt := ((monoAll conditionFuel common (Nat.le_max_left _ _)).expr cfg env condition state).1 _ _ conditionDone
  have branchAt := ((monoAll branchFuel common (Nat.le_max_right _ _)).block cfg env [] yes middle).1 _ _ branchDone
  refine ⟨common + 1, ?_⟩
  simp only [execStmt, bind_apply, conditionAt, expectBool, pure_apply, ite_true, branchAt]

theorem if_then_source_stop {cfg : Cfg} {env : Env} {condition : Expr} {yes : Core.Block}
    {no : Option Core.Block} {origin : OriginId} {state middle after : St} {conditionFuel branchFuel : Nat} {stop : Stop}
    (conditionDone : evalExpr conditionFuel cfg env condition state = .ok (.bool true) middle)
    (branchStopped : execBlock branchFuel cfg env [] yes middle = .stop stop after) (nonTimeout : stop ≠ .timeout) :
    ∃ fuel, execStmt fuel cfg env (.ifS condition yes no origin) state = .stop stop after := by
  let common := max conditionFuel branchFuel
  have conditionAt := ((monoAll conditionFuel common (Nat.le_max_left _ _)).expr cfg env condition state).1 _ _ conditionDone
  rcases ((monoAll branchFuel common (Nat.le_max_right _ _)).block cfg env [] yes middle).2 _ _ branchStopped with timeout | branchAt
  · cases stop <;> simp_all [isTimeout]
  · refine ⟨common + 1, ?_⟩
    simp only [execStmt, bind_apply, conditionAt, expectBool, pure_apply, ite_true, branchAt]

theorem if_false_source_skip {cfg : Cfg} {env : Env} {condition : Expr} {yes : Core.Block}
    {origin : OriginId} {state after : St} {fuel : Nat}
    (conditionDone : evalExpr fuel cfg env condition state = .ok (.bool false) after) :
    execStmt (fuel + 1) cfg env (.ifS condition yes none origin) state = .ok (.normal .unit) after := by
  simp only [execStmt, bind_apply, conditionDone, expectBool, pure_apply, Bool.false_eq_true, ite_false]

#print axioms if_false_source_skip
#print axioms if_then_source_success
#print axioms if_then_source_stop
end Goose.Lower
