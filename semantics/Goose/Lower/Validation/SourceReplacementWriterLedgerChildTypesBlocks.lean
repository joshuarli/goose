import Goose.Lower.Validation.SourceReplacementWriterLedgerChildTypesControls

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR ReplacementContentFlowSource

theorem statementChildren_dead_types {env : LEnv} {loop : Option LoopCtx} {statements : List Stmt}
    {before : LS} (dead : before.cur.isSome = false) :
    statementChildren env loop statements before = statements.map (fun _ => none) := by
  induction statements with
  | nil => rfl
  | cons statement rest ih => simp only [statementChildren, dead, Bool.false_eq_true, ite_false, List.map_cons, ih]

theorem statementChildren_span_types {env : LEnv} {loop : Option LoopCtx} {statements : List Stmt}
    {before start : LS} {child : Fragment}
    (member : some (child, start) ∈ statementChildren env loop statements before) :
    TypePrefix before start ∧ TypePrefix (child.finish env start) (lowerStmts loop statements env before).2 := by
  induction statements generalizing before with
  | nil => simp [statementChildren] at member
  | cons statement rest ih =>
    cases current : before.cur with
    | none => simp [statementChildren_dead_types (env := env) (loop := loop) (statements := statement :: rest) (before := before) (by simp [current])] at member
    | some block =>
      simp only [statementChildren, current, Option.isSome_some, ite_true, List.mem_cons] at member
      have whole : (lowerStmts loop (statement :: rest) env before).2 =
          (lowerStmts loop rest env (lowerStmt loop statement env before).2).2 := by
        simp only [lowerStmts, bind_run, isLive_run current, ite_true]
      rw [whole]
      rcases member with same | member
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
        exact ⟨.refl _, (types_lowerStmts loop rest env _ _ _ rfl)⟩
      · have span := ih member
        exact ⟨(types_lowerStmt loop statement env before _ _ rfl).trans span.1, span.2⟩

theorem Fragment.block_child_span_types {loop : Option LoopCtx} {bindings : List (SlotId × ValueId × OriginId)}
    {want : Bool} {block : Core.Block} {child : Fragment} {env : LEnv} {before start : LS} {index : Nat}
    (row : (Fragment.block loop bindings want block).child? env before index = some (child, start)) :
    TypePrefix before start ∧ TypePrefix (child.finish env start) ((Fragment.block loop bindings want block).finish env before) := by
  have member := Fragment.child_member row
  cases block with
  | mk scope statements value =>
    let entered := (emitEffect (.enter scope) env before).2
    let pushed := (pushScope scope env entered).2
    let initialized := (initSlots bindings env pushed).2
    let stated := (lowerStmts loop statements env initialized).2
    let evaluated := (lowerBlockValue want value env stated).2
    let left := (emitEffect (.leave scope) env evaluated).2
    have whole : ((Fragment.block loop bindings want (.mk scope statements value)).finish env before) =
        (popScope env left).2 := rfl
    have startSpan : TypePrefix before initialized :=
      (types_emitEffect (.enter scope) env before _ _ rfl).trans
        ((types_pushScope scope env entered _ _ rfl).trans (types_initSlots bindings env pushed _ _ rfl))
    have endSpan : TypePrefix evaluated (popScope env left).2 :=
      (types_emitEffect (.leave scope) env evaluated _ _ rfl).trans
        (types_popScope env left _ _ rfl)
    change some (child, start) ∈ statementChildren env loop statements initialized ++
      [value.map fun expression => (.expression expression, stated)] at member
    rw [whole]
    rcases List.mem_append.mp member with statementsMember | valueMember
    · have span := statementChildren_span_types statementsMember
      exact ⟨startSpan.trans span.1, span.2.trans
        ((types_lowerBlockValue want value env stated _ _ rfl).trans endSpan)⟩
    · cases value with
      | none => simp at valueMember
      | some expression =>
        simp only [Option.map_some, List.mem_singleton] at valueMember
        obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj valueMember)
        subst start
        exact ⟨startSpan.trans (types_lowerStmts loop statements env initialized _ _ rfl), endSpan⟩

#print axioms statementChildren_span_types
#print axioms Fragment.block_child_span_types

end Goose.Lower.Validation.SourceReplacementWriterLedger
