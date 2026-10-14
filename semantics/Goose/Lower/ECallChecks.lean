import Goose.Lower.ECall
import Goose.Lower.CallChecks

namespace Goose.Lower.ECallChecks

open Goose.Core Goose.GIR Goose.Lower.CallChecks

def referenceEntry : Impl :=
  { name := "main", params := #[], results := #[], vars := variables,
    body := .mk 0 [.letS 0 (.lit .i64 42) 0,
      .expr (.call 0 [.byRef .readOnly (.var 0)] 0) 0] none, summary := .unknown }

private theorem reference_stmt (profile : NumProfile) (n : Nat) (lc : Option LoopCtx) :
    StatementESimulation n ⟨profile, referenceSource⟩ lc
      (.expr (.call 0 [.byRef .readOnly (.var 0)] 0) 0) := by
  cases n with
  | zero => exact statementESimulation_zero _ _ _
  | succ n => exact stmt_exprE_sim n _ lc _ 0 (concrete_reference_call_expression profile n)

private theorem nil_stmts (profile : NumProfile) (n : Nat) (lc : Option LoopCtx) :
    StatementsESimulation n ⟨profile, referenceSource⟩ lc [] := by
  cases n with
  | zero => exact statementsESimulation_zero _ _ _
  | succ n => exact statementsE_nil n _ lc

private theorem reference_tail (profile : NumProfile) (n : Nat) (lc : Option LoopCtx) :
    StatementsESimulation n ⟨profile, referenceSource⟩ lc
      [.expr (.call 0 [.byRef .readOnly (.var 0)] 0) 0] := by
  cases n with
  | zero => exact statementsESimulation_zero _ _ _
  | succ n =>
    exact statementsE_cons n _ lc _ [] (reference_stmt profile n lc) (nil_stmts profile n lc)

theorem reference_stmts (profile : NumProfile) (n : Nat) (lc : Option LoopCtx) :
    StatementsESimulation n ⟨profile, referenceSource⟩ lc referenceEntry.body.stmts := by
  cases n with
  | zero => exact statementsESimulation_zero _ _ _
  | succ n =>
    exact statementsE_cons n _ lc (.letS 0 (.lit .i64 42) 0) _
      (statementESimulation_fragment n _ lc _ rfl) (reference_tail profile n lc)

theorem reference_block (profile : NumProfile) (n : Nat) (pre : List (VarId × Val)) :
    BlockESimulation n ⟨profile, referenceSource⟩ none (callPre referenceEntry) pre
      false referenceEntry.body := by
  cases n with
  | zero => exact blockESimulation_zero _ _ _ _ _ _
  | succ n =>
    exact blockESimulation_succ n _ none _ pre false 0 _ none
      (reference_stmts profile n none) trivial

theorem actual_calling_callee_block (profile : NumProfile) (n : Nat) :
    CalleeBlockClaim n ⟨profile, referenceSource⟩ 1 referenceEntry :=
  calleeBlockClaim_of_simulation rfl profile n (reference_block profile n)

end Goose.Lower.ECallChecks
