import Goose.Lower.LoopExit
import Goose.Lower.UnwindChecks

namespace Goose.Lower.LoopExitChecks

open Goose.Core Goose.GIR Goose.Lower.UnwindChecks

def loop : LoopCtx := ⟨1, 1, .next 1 .i64 0⟩

def countingBuilder : LS :=
  { blocks := #[⟨[], #[]⟩, ⟨[(0, .data (.int .i64))], #[]⟩],
    vals := #[some (.data (.int .i64))], cur := some 0, stack := [1, 0] }

def continuedBuilder (m : Core.Module) : LS :=
  (lowerStmt (some loop) (.cont 0) (lowerEnv m variables []) countingBuilder).2

def continuationFunction (m : Core.Module) : Func :=
  { scopeFunction with blocks := finishBlocks (continuedBuilder m).blocks }

def counterFrame (current : Int) : GIR.Frame := beforeFrame.set 0 (.val (.int .i64 current))

theorem concrete_counting_continue (cfg : Cfg) (fuel : Nat) (current : Int) :
    SimG ⟨⟨cfg.profile, lower cfg.mod⟩, continuationFunction cfg.mod⟩ (0, 0) (counterFrame current)
      (execStmt fuel cfg beforeEnv (.cont 0) >>= prepareLoopExit beforeEnv 1)
      (fun flow pt' fr' => flow = .cont ∧ NextJumpPost (counterFrame current) 1 0 .i64 current
        [(0, 10)] pt' fr') := by
  apply stmt_cont_next_prepared_sim fuel loop 1 .i64 .i64 0 current 0 rfl
    (lowerEnv cfg.mod variables []) countingBuilder (continuedBuilder cfg.mod) () (0, 0)
    cfg beforeEnv ⟨⟨cfg.profile, lower cfg.mod⟩, continuationFunction cfg.mod⟩ (counterFrame current)
  · exact Frame.set_get _ _ _
  · decide
  · apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  · rfl
  · exact Goose.Proofs.Lower.extT_finish (continuedBuilder cfg.mod)
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · refine ⟨⟨[(0, .data (.int .i64))], []⟩, ?_, rfl⟩
    have hrun : lowerStmt (some loop) (.cont 0) (lowerEnv cfg.mod variables []) countingBuilder =
        ((), continuedBuilder cfg.mod) := Prod.ext (Subsingleton.elim _ _) rfl
    have hkeep := (advB_lowerStmt (some loop) (.cont 0) (lowerEnv cfg.mod variables [])
      countingBuilder () (continuedBuilder cfg.mod) hrun).keep 1
        ⟨[(0, .data (.int .i64))], #[]⟩ (by decide) rfl
    change (finishBlocks (continuedBuilder cfg.mod).blocks)[1]? = _
    simp [finishBlocks, Array.getElem?_map, hkeep]

def jumpLoop : LoopCtx := ⟨1, 1, .jump 1⟩

def jumpBuilder : LS :=
  { blocks := #[⟨[], #[]⟩, ⟨[], #[]⟩], vals := #[], cur := some 0, stack := [1, 0] }

def jumpedBuilder (m : Core.Module) (stmt : Stmt) : LS :=
  (lowerStmt (some jumpLoop) stmt (lowerEnv m variables []) jumpBuilder).2

def jumpFunction (m : Core.Module) (stmt : Stmt) : Func :=
  { scopeFunction with blocks := finishBlocks (jumpedBuilder m stmt).blocks }

theorem concrete_break (cfg : Cfg) (fuel : Nat) :
    SimG ⟨⟨cfg.profile, lower cfg.mod⟩, jumpFunction cfg.mod (.brk 0)⟩ (0, 0) beforeFrame
      (execStmt fuel cfg beforeEnv (.brk 0) >>= prepareLoopExit beforeEnv 1)
      (fun flow pt' fr' => flow = .brk ∧ JumpPost beforeFrame 1 [(0, 10)] pt' fr') := by
  apply stmt_brk_prepared_sim fuel jumpLoop 0 (lowerEnv cfg.mod variables [])
    jumpBuilder (jumpedBuilder cfg.mod (.brk 0)) () (0, 0) cfg beforeEnv
    ⟨⟨cfg.profile, lower cfg.mod⟩, jumpFunction cfg.mod (.brk 0)⟩ beforeFrame
  · apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  · rfl
  · exact Goose.Proofs.Lower.extT_finish (jumpedBuilder cfg.mod (.brk 0))
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · refine ⟨⟨[], []⟩, ?_, rfl⟩
    have hrun : lowerStmt (some jumpLoop) (.brk 0) (lowerEnv cfg.mod variables []) jumpBuilder =
        ((), jumpedBuilder cfg.mod (.brk 0)) := Prod.ext (Subsingleton.elim _ _) rfl
    have hkeep := (advB_lowerStmt (some jumpLoop) (.brk 0) (lowerEnv cfg.mod variables [])
      jumpBuilder () (jumpedBuilder cfg.mod (.brk 0)) hrun).keep 1 ⟨[], #[]⟩ (by decide) rfl
    change (finishBlocks (jumpedBuilder cfg.mod (.brk 0)).blocks)[1]? = _
    simp [finishBlocks, Array.getElem?_map, hkeep]

theorem concrete_while_continue (cfg : Cfg) (fuel : Nat) :
    SimG ⟨⟨cfg.profile, lower cfg.mod⟩, jumpFunction cfg.mod (.cont 0)⟩ (0, 0) beforeFrame
      (execStmt fuel cfg beforeEnv (.cont 0) >>= prepareLoopExit beforeEnv 1)
      (fun flow pt' fr' => flow = .cont ∧ JumpPost beforeFrame 1 [(0, 10)] pt' fr') := by
  apply stmt_cont_jump_prepared_sim fuel jumpLoop 1 0 rfl (lowerEnv cfg.mod variables [])
    jumpBuilder (jumpedBuilder cfg.mod (.cont 0)) () (0, 0) cfg beforeEnv
    ⟨⟨cfg.profile, lower cfg.mod⟩, jumpFunction cfg.mod (.cont 0)⟩ beforeFrame
  · apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  · rfl
  · exact Goose.Proofs.Lower.extT_finish (jumpedBuilder cfg.mod (.cont 0))
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · refine ⟨⟨[], []⟩, ?_, rfl⟩
    have hrun : lowerStmt (some jumpLoop) (.cont 0) (lowerEnv cfg.mod variables []) jumpBuilder =
        ((), jumpedBuilder cfg.mod (.cont 0)) := Prod.ext (Subsingleton.elim _ _) rfl
    have hkeep := (advB_lowerStmt (some jumpLoop) (.cont 0) (lowerEnv cfg.mod variables [])
      jumpBuilder () (jumpedBuilder cfg.mod (.cont 0)) hrun).keep 1 ⟨[], #[]⟩ (by decide) rfl
    change (finishBlocks (jumpedBuilder cfg.mod (.cont 0)).blocks)[1]? = _
    simp [finishBlocks, Array.getElem?_map, hkeep]

end Goose.Lower.LoopExitChecks
