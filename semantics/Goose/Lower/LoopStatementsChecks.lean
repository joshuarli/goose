import Goose.Lower.LoopStatements
import Goose.Lower.LoopExitChecks

namespace Goose.Lower.LoopStatementsChecks

open Goose.Core Goose.GIR Goose.Lower.UnwindChecks Goose.Lower.LoopExitChecks

def breakingList : List Stmt := [.expr (.lit .i64 99) 0, .brk 0]

def listBuilder (m : Core.Module) : LS :=
  (lowerStmts (some jumpLoop) breakingList (lowerEnv m variables) jumpBuilder).2

def listFunction (m : Core.Module) : Func :=
  { scopeFunction with blocks := finishBlocks (listBuilder m).blocks }

private theorem nil_sim (cfg : Cfg) (fuel : Nat) :
    StatementsLoopSimulation fuel cfg (some jumpLoop) [] := by
  cases fuel with
  | zero => exact statementsLoopSimulation_zero _ _ _
  | succ n => exact statementsLoop_nil n _ _

private theorem break_sim (cfg : Cfg) (fuel : Nat) :
    StatementsLoopSimulation fuel cfg (some jumpLoop) [.brk 0] := by
  cases fuel with
  | zero => exact statementsLoopSimulation_zero _ _ _
  | succ n =>
    exact statementsLoop_cons n cfg (some jumpLoop) (.brk 0) []
      (statementLoopSimulation_break n cfg jumpLoop 0) (nil_sim cfg n)

theorem breaking_list_sim (cfg : Cfg) (fuel : Nat) :
    StatementsLoopSimulation fuel cfg (some jumpLoop) breakingList := by
  cases fuel with
  | zero => exact statementsLoopSimulation_zero _ _ _
  | succ n =>
    exact statementsLoop_cons n cfg (some jumpLoop) (.expr (.lit .i64 99) 0) [.brk 0]
      (StatementESimulation.toLoop (statementESimulation_fragment n cfg _ _ rfl))
      (break_sim cfg n)

theorem concrete_breaking_list (cfg : Cfg) (fuel : Nat) :
    SimE ⟨⟨cfg.profile, lower cfg.mod⟩, listFunction cfg.mod⟩ (0, 0) beforeFrame
      (execStmts fuel cfg beforeEnv breakingList >>= prepareLoopFlow beforeEnv (some jumpLoop))
      (StatementLoopPost cfg beforeEnv ⟨⟨cfg.profile, lower cfg.mod⟩, listFunction cfg.mod⟩
        jumpBuilder beforeFrame (listBuilder cfg.mod) (some jumpLoop)) := by
  apply breaking_list_sim cfg fuel (lowerEnv cfg.mod variables) jumpBuilder (listBuilder cfg.mod)
    () (0, 0) beforeEnv ⟨⟨cfg.profile, lower cfg.mod⟩, listFunction cfg.mod⟩ beforeFrame
  · exact Prod.ext (Subsingleton.elim _ _) rfl
  · rfl
  · exact Goose.Proofs.Lower.extT_finish (listBuilder cfg.mod)
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rfl
  · rfl
  · change jumpLoop.depth ≤ beforeEnv.scopes.length
    decide
  · have htarget : ∃ block, (listFunction cfg.mod).blocks[1]? = some block ∧ block.params = [] := by
      have hlow : lowerStmts (some jumpLoop) breakingList (lowerEnv cfg.mod variables)
          jumpBuilder = ((), listBuilder cfg.mod) := Prod.ext (Subsingleton.elim _ _) rfl
      have hkeep := (advB_lowerStmts (some jumpLoop) breakingList (lowerEnv cfg.mod variables)
        jumpBuilder () (listBuilder cfg.mod) hlow).keep 1 ⟨[], #[]⟩ (by decide) rfl
      refine ⟨⟨[], []⟩, ?_, rfl⟩
      change (finishBlocks (listBuilder cfg.mod).blocks)[1]? = _
      simp [finishBlocks, Array.getElem?_map, hkeep]
    exact ⟨htarget, htarget⟩
  · trivial

end Goose.Lower.LoopStatementsChecks
