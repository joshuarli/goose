import Goose.Lower.Validation.ReplacementContentFlowSourceReadyBuilder
import Goose.Lower.Validation.OperandStatements

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem lowerExprs_ready (state : State) (expressions : List Expr) (env : LEnv) (initial : LS)
    (step : ∀ earlier expression suffix, expressions = earlier ++ expression :: suffix →
      ValueReadyAt state (lowerExpr expression) env (lowerExprs earlier env initial).2) :
    ValuesReadyAt state (lowerExprs expressions) env initial := by
  induction expressions generalizing initial with
  | nil => exact ⟨EmitsOnly.refl _ _, by simp [lowerExprs, pure_run]⟩
  | cons expression rest ih =>
    have first := step [] expression rest rfl
    simp only [lowerExprs, pure_run] at first
    have tail := ih (lowerExpr expression env initial).2 (by
      intro earlier child suffix split
      have selected := step (expression :: earlier) child suffix (by simp [split])
      simpa only [lowerExprs, bind_run, pure_run] using selected)
    refine ⟨?_, ?_⟩
    · simpa only [lowerExprs, bind_run, pure_run] using first.1.trans tail.1
    · intro live value member
      simp only [lowerExprs, bind_run, pure_run] at live member
      rcases List.mem_cons.mp member with same | later
      · subst value
        exact first.2 ((dead_lowerExprs rest).live_before rfl live)
      · exact tail.2 live value later

theorem lowerArgs_ready (state : State) (arguments : List Arg) (env : LEnv) (initial : LS)
    (step : ∀ earlier argument suffix, arguments = earlier ++ argument :: suffix →
      ValueReadyAt state (lowerArg argument) env (lowerArgs earlier env initial).2) :
    ValuesReadyAt state (lowerArgs arguments) env initial := by
  induction arguments generalizing initial with
  | nil => exact ⟨EmitsOnly.refl _ _, by simp [lowerArgs, pure_run]⟩
  | cons argument rest ih =>
    have first := step [] argument rest rfl
    simp only [lowerArgs, pure_run] at first
    have tail := ih (lowerArg argument env initial).2 (by
      intro earlier child suffix split
      have selected := step (argument :: earlier) child suffix (by simp [split])
      simpa only [lowerArgs, bind_run, pure_run] using selected)
    refine ⟨?_, ?_⟩
    · simpa only [lowerArgs, bind_run, pure_run] using first.1.trans tail.1
    · intro live value member
      simp only [lowerArgs, bind_run, pure_run] at live member
      rcases List.mem_cons.mp member with same | later
      · subst value
        exact first.2 ((dead_lowerArgs rest).live_before rfl live)
      · exact tail.2 live value later

def PrintArgumentsReadyAt (state : State) (arguments : List PrintArg) (env : LEnv) (initial : LS) : Prop :=
  EmitsOnly (ReadyOperands state) initial (lowerPrintArgs arguments env initial).2 ∧
    ((lowerPrintArgs arguments env initial).2.cur.isSome = true →
      ∀ value, PrintPart.val value ∈ (lowerPrintArgs arguments env initial).1 →
        flowAt state.values value ≠ .pending)

theorem lowerPrintArgs_ready (state : State) (arguments : List PrintArg) (env : LEnv) (initial : LS)
    (step : ∀ earlier expression suffix, arguments = earlier ++ .expr expression :: suffix →
      ValueReadyAt state (lowerExpr expression) env (lowerPrintArgs earlier env initial).2) :
    PrintArgumentsReadyAt state arguments env initial := by
  induction arguments generalizing initial with
  | nil => exact ⟨EmitsOnly.refl _ _, by simp [lowerPrintArgs, pure_run]⟩
  | cons argument rest ih =>
    cases argument with
    | text text =>
      have tail := ih initial (by
        intro earlier expression suffix split
        have selected := step (.text text :: earlier) expression suffix (by simp [split])
        simpa only [lowerPrintArgs, bind_run, pure_run] using selected)
      refine ⟨?_, ?_⟩
      · simpa only [lowerPrintArgs, bind_run, pure_run] using tail.1
      · intro live value member
        simp only [lowerPrintArgs, bind_run, pure_run] at member
        rcases List.mem_cons.mp member with impossible | later
        · cases impossible
        · exact tail.2 live value later
    | expr expression =>
      have first := step [] expression rest rfl
      simp only [lowerPrintArgs, pure_run] at first
      have tail := ih (lowerExpr expression env initial).2 (by
        intro earlier child suffix split
        have selected := step (.expr expression :: earlier) child suffix (by simp [split])
        simpa only [lowerPrintArgs, bind_run, pure_run] using selected)
      refine ⟨?_, ?_⟩
      · simpa only [lowerPrintArgs, bind_run, pure_run] using first.1.trans tail.1
      · intro live value member
        simp only [lowerPrintArgs, bind_run, pure_run] at live member
        rcases List.mem_cons.mp member with same | later
        · cases same
          exact first.2 ((dead_lowerPrintArgs rest).live_before rfl live)
        · exact tail.2 live value later

#print axioms lowerExprs_ready
#print axioms lowerArgs_ready
#print axioms lowerPrintArgs_ready

end Goose.Lower.Validation.ReplacementContentFlowSource
