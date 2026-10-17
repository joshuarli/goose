import Goose.Lower.Validation.SourceReplacementWriterLedger

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

theorem bind_suffix_ext {α β : Type} (first : B α) (next : α → B β)
    (advancing : ∀ value, AdvB (next value)) (env : LEnv) (before : LS) :
    (first env before).2.Ext ((first >>= next) env before).2 := by
  exact (advancing (first env before).1 env (first env before).2 _ _ rfl).ext

theorem Fragment.child_member {fragment child : Fragment} {env : LEnv} {before start : LS}
    {index : Nat} (row : fragment.child? env before index = some (child, start)) :
    some (child, start) ∈ fragment.children env before := by
  cases found : (fragment.children env before)[index]? with
  | none => simp [Fragment.child?, found] at row
  | some entry =>
    have same : entry = some (child, start) := by simpa only [Fragment.child?, found, Option.join_some] using row
    exact same ▸ List.mem_of_getElem? found

theorem expressionChildren_span {env : LEnv} {expressions : List Expr} {before start : LS} {child : Fragment}
    (member : some (child, start) ∈ expressionChildren env expressions before) :
    before.Ext start ∧ (child.finish env start).Ext (lowerExprs expressions env before).2 := by
  induction expressions generalizing before with
  | nil => simp [expressionChildren] at member
  | cons expression rest ih =>
    simp only [expressionChildren, List.mem_cons] at member
    rcases member with same | member
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      refine ⟨.refl _, ?_⟩
      exact bind_suffix_ext (lowerExpr expression)
        (fun value => do let values ← lowerExprs rest; pure (value :: values))
        (fun _ => AdvB.bind (advB_lowerExprs rest) (fun _ => AdvB.pure _)) env start
    · have span := ih member
      refine ⟨(advB_lowerExpr expression env before _ _ rfl).ext.trans span.1, ?_⟩
      simpa only [lowerExprs, bind_run, pure_run] using span.2

theorem argumentChildren_span {env : LEnv} {arguments : List Arg} {before start : LS} {child : Fragment}
    (member : some (child, start) ∈ argumentChildren env arguments before) :
    before.Ext start ∧ (child.finish env start).Ext (lowerArgs arguments env before).2 := by
  induction arguments generalizing before with
  | nil => simp [argumentChildren] at member
  | cons argument rest ih =>
    simp only [argumentChildren, List.mem_cons] at member
    have suffix := bind_suffix_ext (lowerArg argument)
      (fun value => do let values ← lowerArgs rest; pure (value :: values))
      (fun _ => AdvB.bind (advB_lowerArgs rest) (fun _ => AdvB.pure _)) env before
    rcases member with same | member
    · cases argument with
      | byVal expression =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
        exact ⟨.refl _, suffix⟩
      | byRef mutability place =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
        exact ⟨.refl _, (bind_suffix_ext (lowerPlace place) (borrowTo mutability)
          (advB_borrowTo mutability) env start).trans suffix⟩
    · have span := ih member
      refine ⟨(advB_lowerArg argument env before _ _ rfl).ext.trans span.1, ?_⟩
      simpa only [lowerArgs, bind_run, pure_run] using span.2

theorem printChildren_span {env : LEnv} {arguments : List PrintArg} {before start : LS} {child : Fragment}
    (member : some (child, start) ∈ printChildren env arguments before) :
    before.Ext start ∧ (child.finish env start).Ext (lowerPrintArgs arguments env before).2 := by
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
        exact bind_suffix_ext (lowerExpr expression)
          (fun value => do let values ← lowerPrintArgs rest; pure (.val value :: values))
          (fun _ => AdvB.bind (advB_lowerPrintArgs rest) (fun _ => AdvB.pure _)) env start
      · have span := ih member
        refine ⟨(advB_lowerExpr expression env before _ _ rfl).ext.trans span.1, ?_⟩
        simpa only [lowerPrintArgs, bind_run, pure_run] using span.2

#print axioms expressionChildren_span
#print axioms argumentChildren_span
#print axioms printChildren_span

end Goose.Lower.Validation.SourceReplacementWriterLedger
