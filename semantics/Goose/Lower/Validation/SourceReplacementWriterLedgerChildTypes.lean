import Goose.Lower.Validation.SourceReplacementWriterLedgerChildSpans
import Goose.Lower.Validation.ValueTypes

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

theorem bind_suffix_ext_types {α β : Type} (first : B α) (next : α → B β)
    (advancing : ∀ value, TypeRun (next value)) (env : LEnv) (before : LS) :
    TypePrefix (first env before).2 ((first >>= next) env before).2 := by
  exact (advancing (first env before).1 env (first env before).2 _ _ rfl)

theorem expressionChildren_span_types {env : LEnv} {expressions : List Expr} {before start : LS} {child : Fragment}
    (member : some (child, start) ∈ expressionChildren env expressions before) :
    TypePrefix before start ∧ TypePrefix (child.finish env start) (lowerExprs expressions env before).2 := by
  induction expressions generalizing before with
  | nil => simp [expressionChildren] at member
  | cons expression rest ih =>
    simp only [expressionChildren, List.mem_cons] at member
    rcases member with same | member
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      refine ⟨.refl _, ?_⟩
      exact bind_suffix_ext_types (lowerExpr expression)
        (fun value => do let values ← lowerExprs rest; pure (value :: values))
        (fun _ => TypeRun.bind (types_lowerExprs rest) (fun _ => TypeRun.pure _)) env start
    · have span := ih member
      refine ⟨(types_lowerExpr expression env before _ _ rfl).trans span.1, ?_⟩
      simpa only [lowerExprs, bind_run, pure_run] using span.2

theorem argumentChildren_span_types {env : LEnv} {arguments : List Arg} {before start : LS} {child : Fragment}
    (member : some (child, start) ∈ argumentChildren env arguments before) :
    TypePrefix before start ∧ TypePrefix (child.finish env start) (lowerArgs arguments env before).2 := by
  induction arguments generalizing before with
  | nil => simp [argumentChildren] at member
  | cons argument rest ih =>
    simp only [argumentChildren, List.mem_cons] at member
    have suffix := bind_suffix_ext_types (lowerArg argument)
      (fun value => do let values ← lowerArgs rest; pure (value :: values))
      (fun _ => TypeRun.bind (types_lowerArgs rest) (fun _ => TypeRun.pure _)) env before
    rcases member with same | member
    · cases argument with
      | byVal expression =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
        exact ⟨.refl _, suffix⟩
      | byRef mutability place =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
        exact ⟨.refl _, (bind_suffix_ext_types (lowerPlace place) (borrowTo mutability)
          (types_borrowTo mutability) env start).trans suffix⟩
    · have span := ih member
      refine ⟨(types_lowerArg argument env before _ _ rfl).trans span.1, ?_⟩
      simpa only [lowerArgs, bind_run, pure_run] using span.2

theorem printChildren_span_types {env : LEnv} {arguments : List PrintArg} {before start : LS} {child : Fragment}
    (member : some (child, start) ∈ printChildren env arguments before) :
    TypePrefix before start ∧ TypePrefix (child.finish env start) (lowerPrintArgs arguments env before).2 := by
  induction arguments generalizing before with
  | nil => simp [printChildren] at member
  | cons argument rest ih =>
    cases argument with
    | text value =>
      have span := ih (by simpa only [printChildren, List.mem_cons, Option.some_ne_none, false_or] using member)
      exact ⟨span.1, by simpa only [lowerPrintArgs, bind_run, pure_run] using span.2⟩
    | expr expression =>
      simp only [printChildren, List.mem_cons] at member
      rcases member with same | member
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
        refine ⟨.refl _, ?_⟩
        exact bind_suffix_ext_types (lowerExpr expression)
          (fun value => do let values ← lowerPrintArgs rest; pure (.val value :: values))
          (fun _ => TypeRun.bind (types_lowerPrintArgs rest) (fun _ => TypeRun.pure _)) env start
      · have span := ih member
        refine ⟨(types_lowerExpr expression env before _ _ rfl).trans span.1, ?_⟩
        simpa only [lowerPrintArgs, bind_run, pure_run] using span.2

#print axioms expressionChildren_span_types
#print axioms argumentChildren_span_types
#print axioms printChildren_span_types

end Goose.Lower.Validation.SourceReplacementWriterLedger
