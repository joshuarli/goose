import Goose.Lower.Validation.ReplacementScopedOperandsConditionals

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem rhs_freshPrintArgs : ∀ args : List PrintArg, ∀ env before parts after,
    lowerPrintArgs args env before = (parts, after) → after.cur.isSome = true →
    ∀ value ∈ parts.flatMap PrintPart.uses, before.vals.size ≤ value
  | [], env, before, parts, after, run, live => by
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    simp
  | .text text :: rest, env, before, parts, after, run, live => by
    simp only [lowerPrintArgs, bind_eq] at run
    obtain ⟨tail, middle, tailRun, pureRun⟩ := run
    obtain ⟨rfl, rfl⟩ := pure_eq.mp pureRun
    simpa only [List.flatMap_cons, PrintPart.uses, List.nil_append] using
      rhs_freshPrintArgs rest env before tail middle tailRun live
  | .expr expr :: rest, env, before, parts, after, run, live => by
    simp only [lowerPrintArgs, bind_eq] at run
    obtain ⟨head, middle, headRun, tail, ended, tailRun, pureRun⟩ := run
    obtain ⟨rfl, rfl⟩ := pure_eq.mp pureRun
    intro value member
    simp only [List.flatMap_cons, PrintPart.uses, List.singleton_append, List.mem_cons] at member
    rcases member with rfl | member
    · exact freshValue_lowerExpr expr env before _ middle headRun
        (live_before (dead_lowerPrintArgs rest) tailRun live)
    · exact Nat.le_trans (advB_lowerExpr expr env before _ middle headRun).vals
        (rhs_freshPrintArgs rest env middle tail ended tailRun live value member)

theorem rhsOperands_print (floor : Nat) (loop : Option LoopCtx) (args : List PrintArg) (origin : OriginId)
    (child : RhsOperandsRun floor (lowerPrintArgs args)) :
    RhsOperandsRun floor (lowerStmt loop (.print args origin)) := by
  intro env before bound
  simp only [lowerStmt]
  apply RhsOperandsAt.bindRun (child env before bound)
  intro parts middle run
  exact RhsOperandsAt.emitEffect _ _ _ _ fun live value member =>
    Nat.le_trans bound (rhs_freshPrintArgs args env before parts middle run live value member)

theorem rhsOperands_return (floor : Nat) (loop : Option LoopCtx) (value : Option Expr) (origin : OriginId)
    (child : ∀ expr, value = some expr → RhsOperandsRun floor (lowerExpr expr)) :
    RhsOperandsRun floor (lowerStmt loop (.ret value origin)) := by
  cases value with
  | none =>
    intro env before bound
    simp only [lowerStmt]
    apply (RhsOperandsAt.pure _ _ _ _).bind
    exact (RhsOperandsAt.leaveTo _ _ _ _).bind
      (RhsOperandsAt.emitTerm _ _ _ _ (by simp [pure_run, Term.uses]))
  | some expr =>
    intro env before bound
    simp only [lowerStmt]
    apply RhsOperandsAt.bindFresh bound (child expr rfl env before bound)
      (advB_lowerExpr expr) (freshValue_lowerExpr expr)
    intro result evaluated _ evaluatedBound resultFresh
    apply RhsOperandsAt.bindRun
      (RhsOperandsAt.coerceResult _ _ _ _ _ evaluatedBound resultFresh)
    intro coerced converted coerceRun
    have coercedFresh := RhsValueFresh.coerceResult evaluatedBound resultFresh coerceRun
    apply (RhsOperandsAt.pure _ _ _ _).bind
    apply RhsOperandsAt.bindRun (RhsOperandsAt.leaveTo _ _ _ _)
    intro result ended leaveRun
    have retained := coercedFresh.after (dead_leaveTo _) leaveRun
    exact RhsOperandsAt.emitTerm _ _ _ _ (by simpa only [pure_run, Term.uses, List.mem_singleton] using
      fun live used equal => equal ▸ retained live)

theorem rhsOperands_exit (floor : Nat) (loop : Option LoopCtx) (value : Expr) (origin : OriginId)
    (child : RhsOperandsRun floor (lowerExpr value)) :
    RhsOperandsRun floor (lowerStmt loop (.exit value origin)) := by
  intro env before bound
  simp only [lowerStmt]
  apply RhsOperandsAt.bindFresh bound (child env before bound)
    (advB_lowerExpr value) (freshValue_lowerExpr value)
  intro result evaluated _ _ resultFresh
  exact RhsOperandsAt.emitTerm _ _ _ _ (by simpa only [Term.uses, List.mem_singleton] using
    fun live used equal => equal ▸ resultFresh live)

end Goose.Lower.Validation
