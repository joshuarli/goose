import Goose.Lower.Validation.SourceReadyBlocksPrimitives
import Goose.Lower.Validation.SourceStatementTypingBlocks

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem lowerStmts_ready {state : State} {env : LEnv} {before : LS}
    {typingEnv output : TEnv} {scope start finish : Nat} {loop : Option LoopCtx} {statements : List Stmt}
    (source : Core.tyStmts typingEnv scope statements start = .ok (output, finish))
    (visible : VisibleSlotsReady typingEnv state)
    (child : ∀ earlier statement later prefixEnv nextEnv prefixOffset nextOffset,
      statements = earlier ++ statement :: later →
      Core.tyStmts typingEnv scope earlier start = .ok (prefixEnv, prefixOffset) →
      Core.tyStmt prefixEnv scope statement prefixOffset = .ok (nextEnv, nextOffset) →
      VisibleSlotsReady prefixEnv state →
      (lowerStmts loop earlier env before).2.cur.isSome = true →
      EmitsOnly (ReadyOperands state) (lowerStmts loop earlier env before).2
        (lowerStmt loop statement env (lowerStmts loop earlier env before).2).2 ∧
      ((lowerStmt loop statement env (lowerStmts loop earlier env before).2).2.cur.isSome = true →
        VisibleSlotsReady nextEnv state)) :
    EmitsOnly (ReadyOperands state) before (lowerStmts loop statements env before).2 ∧
      ((lowerStmts loop statements env before).2.cur.isSome = true → VisibleSlotsReady output state) := by
  induction statements generalizing typingEnv start before with
  | nil =>
    have same : output = typingEnv := (congrArg Prod.fst ((st_pure_ok _ _ _).mp source))
    subst output
    exact ⟨.refl _ _, fun _ => visible⟩
  | cons statement rest ih =>
    obtain ⟨middle, next, checked, remaining⟩ := tyStmts_cons_children source
    cases current : before.cur with
    | none =>
      simp only [lowerStmts, bind_run, isLive_none current, Bool.false_eq_true, reduceIte, pure_run]
      exact ⟨.refl _ _, by simp [current]⟩
    | some block =>
      have active := isLive_run (le := env) current
      have first := child [] statement rest typingEnv middle start next rfl rfl checked visible (by
        simp [lowerStmts, pure_run, current])
      simp only [lowerStmts, pure_run] at first
      by_cases live : (lowerStmt loop statement env before).2.cur.isSome = true
      · have tail := ih (before := (lowerStmt loop statement env before).2) remaining (first.2 live) (by
          intro earlier selected later prefixEnv nextEnv prefixOffset nextOffset split prefixSource selectedSource prefixVisible prefixLive
          have prefixChecked : Core.tyStmts typingEnv scope (statement :: earlier) start =
              .ok (prefixEnv, prefixOffset) := by
            exact (st_bind_ok _ _ _ _).mpr ⟨middle, next, checked, prefixSource⟩
          have selectedReady := child (statement :: earlier) selected later prefixEnv nextEnv prefixOffset nextOffset
            (by simp [split]) prefixChecked selectedSource prefixVisible
          simpa only [lowerStmts, bind_run, active, reduceIte] using selectedReady (by simpa only [lowerStmts, bind_run, active, reduceIte] using prefixLive))
        simpa only [lowerStmts, bind_run, active, reduceIte] using
          And.intro (first.1.trans tail.1) tail.2
      · have dead : (lowerStmt loop statement env before).2.cur = none := by
          cases h : (lowerStmt loop statement env before).2.cur <;> simp_all
        cases rest with
        | nil =>
          simp only [Core.tyStmts] at remaining
          have same : output = middle := (congrArg Prod.fst ((st_pure_ok _ _ _).mp remaining))
          subst output
          simpa only [lowerStmts, bind_run, active, reduceIte, pure_run] using first
        | cons nextStmt tail =>
          simpa only [lowerStmts, bind_run, active, reduceIte, isLive_none dead,
            Bool.false_eq_true, pure_run] using And.intro first.1
              (show (lowerStmt loop statement env before).2.cur.isSome = true → VisibleSlotsReady output state from
                by simp [dead])

#print axioms lowerStmts_ready

end Goose.Lower.Validation.ReplacementContentFlowSource
