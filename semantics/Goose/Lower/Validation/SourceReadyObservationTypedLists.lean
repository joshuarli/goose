import Goose.Lower.Validation.ReplacementContentFlowSourceReadyLists
import Goose.Lower.Validation.SourceReadyObservationValues
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes
import Goose.Lower.Validation.ExpressionTypingAggregateOps

namespace Goose.Lower.Validation.ReplacementContentFlowSource.SourceReadyExpressionListObservations

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

private theorem typed_struct_expression_checkpoint {env : TEnv} {fields : List Ty}
    {earlier later : List Expr} {expression : Expr} {start finish : Nat}
    (source : Core.tyStructExprs env fields (earlier ++ expression :: later) start = .ok ((), finish)) :
    ∃ type childStart childFinish, Core.tyExpr env expression childStart = .ok (type, childFinish) := by
  induction earlier generalizing fields start with
  | nil =>
    cases fields with
    | nil => exact (rej_ok _ _ _ _).mp source |>.elim
    | cons expected fields =>
      simp only [List.nil_append, Core.tyStructExprs] at source
      obtain ⟨type, next, typed, _⟩ := (st_bind_ok _ _ _ _).mp source
      exact ⟨type, start, next, typed⟩
  | cons first earlier ih =>
    cases fields with
    | nil => exact (rej_ok _ _ _ _).mp source |>.elim
    | cons expected fields =>
      simp only [List.cons_append, Core.tyStructExprs] at source
      obtain ⟨type, next, _, source⟩ := (st_bind_ok _ _ _ _).mp source
      by_cases equal : (type == expected) = true
      · simp only [equal, ite_true] at source
        exact ih source
      · simp [equal, chk] at source

private theorem lower_exprs_append_run (earlier later : List Expr) (env : LEnv) (initial : LS) :
    lowerExprs (earlier ++ later) env initial =
      let first := lowerExprs earlier env initial
      let last := lowerExprs later env first.2
      (first.1 ++ last.1, last.2) := by
  induction earlier generalizing initial with
  | nil => simp only [List.nil_append, lowerExprs, pure_run, List.nil_append]
  | cons expression rest ih =>
    simpa only [List.cons_append, lowerExprs, bind_run, pure_run] using
      congrArg (fun result : List ValueId × LS =>
        ((lowerExpr expression env initial).1 :: result.1, result.2))
        (ih (lowerExpr expression env initial).2)

private theorem expressions_ready {module : GIR.Module} {func : Func} (state : State)
    (expressions : List Expr) (env : LEnv) (initial : LS)
    (step : ∀ earlier expression suffix, expressions = earlier ++ expression :: suffix →
      ValueReadyAt state (lowerExpr expression) env (lowerExprs earlier env initial).2 ∧
      EmitsOnly (ReadyCallObservations module func state) (lowerExprs earlier env initial).2
        (lowerExpr expression env (lowerExprs earlier env initial).2).2) :
    ValuesReadyAt state (lowerExprs expressions) env initial ∧
      EmitsOnly (ReadyCallObservations module func state) initial (lowerExprs expressions env initial).2 := by
  induction expressions generalizing initial with
  | nil => exact ⟨⟨.refl _ _, by simp [lowerExprs, pure_run]⟩, .refl _ _⟩
  | cons expression rest ih =>
    have first := step [] expression rest rfl
    simp only [lowerExprs, pure_run] at first
    have tail := ih (lowerExpr expression env initial).2 (by
      intro earlier child suffix split
      have selected := step (expression :: earlier) child suffix (by simp [split])
      simpa only [lowerExprs, bind_run, pure_run] using selected)
    refine ⟨⟨?_, ?_⟩, ReadyCallObservations.expressionsCons expression rest first.2 tail.2⟩
    · exact first.1.1.trans tail.1.1
    · intro live value member
      simp only [lowerExprs, bind_run, pure_run] at live member
      rcases List.mem_cons.mp member with same | later
      · subst value
        exact first.1.2 ((dead_lowerExprs rest).live_before rfl live)
      · exact tail.1.2 live value later

variable {module : GIR.Module} {func : Func}
  {types : Array (Option VTy)} {state : State} {completed initial : LS}
  {typingEnv : TEnv} {results : List Ty} {start finish : Nat}

theorem typedStructExpressions {fields : List Ty} {expressions : List Expr}
    (source : Core.tyStructExprs typingEnv fields expressions start = .ok ((), finish))
    (generated : GeneratedBuilderState initial)
    (native : NativeRows types (lowerExprs expressions (lowerEnv typingEnv.mod typingEnv.vars results) initial).2)
    (extension : (lowerExprs expressions (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.Ext completed)
    (allocated : (lowerExprs expressions (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (expressionChild : ∀ earlier expression later, expressions = earlier ++ expression :: later →
      ∀ type childStart childFinish,
      Core.tyExpr typingEnv expression childStart = .ok (type, childFinish) →
      let before := (lowerExprs earlier (lowerEnv typingEnv.mod typingEnv.vars results) initial).2
      GeneratedBuilderState before →
      NativeRows types (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      (ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) before) ∧
      EmitsOnly (ReadyCallObservations module func state) before
        (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2) :
    ValuesReadyAt state (lowerExprs expressions) (lowerEnv typingEnv.mod typingEnv.vars results) initial ∧
      EmitsOnly (ReadyCallObservations module func state) initial
        (lowerExprs expressions (lowerEnv typingEnv.mod typingEnv.vars results) initial).2 := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  change NativeRows types (lowerExprs expressions env initial).2 at native
  change (lowerExprs expressions env initial).2.Ext completed at extension
  change (lowerExprs expressions env initial).2.vals.size ≤ completed.vals.size at allocated
  apply expressions_ready state expressions env initial
  intro earlier expression later split
  obtain ⟨type, childStart, childFinish, childSource⟩ := typed_struct_expression_checkpoint
    (by rw [← split]; exact source)
  let before := (lowerExprs earlier env initial).2
  let child := lowerExpr expression env before
  have suffix : (lowerExprs later env child.2).2 = (lowerExprs expressions env initial).2 := by
    rw [split, lower_exprs_append_run]
    rfl
  have advance : child.2.Adv (lowerExprs expressions env initial).2 := by
    rw [← suffix]
    exact advB_lowerExprs later env child.2 _ _ rfl
  have childNative : NativeRows types child.2 := by
    apply native.of_prefix
    rw [← suffix]
    exact types_lowerExprs later env child.2 _ _ rfl
  exact expressionChild earlier expression later split type childStart childFinish childSource
    (generated.lowerExprs earlier rfl) childNative (advance.ext.trans extension)
    (Nat.le_trans advance.vals allocated) visible

theorem typedExpressionsAs {element : Ty} {expressions : List Expr}
    (source : Core.tyExprsAs typingEnv element expressions start = .ok ((), finish))
    (generated : GeneratedBuilderState initial)
    (native : NativeRows types (lowerExprs expressions (lowerEnv typingEnv.mod typingEnv.vars results) initial).2)
    (extension : (lowerExprs expressions (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.Ext completed)
    (allocated : (lowerExprs expressions (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (expressionChild : ∀ earlier expression later, expressions = earlier ++ expression :: later →
      ∀ type childStart childFinish,
      Core.tyExpr typingEnv expression childStart = .ok (type, childFinish) →
      let before := (lowerExprs earlier (lowerEnv typingEnv.mod typingEnv.vars results) initial).2
      GeneratedBuilderState before →
      NativeRows types (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      (ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) before) ∧
      EmitsOnly (ReadyCallObservations module func state) before
        (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2) :
    ValuesReadyAt state (lowerExprs expressions) (lowerEnv typingEnv.mod typingEnv.vars results) initial ∧
      EmitsOnly (ReadyCallObservations module func state) initial
        (lowerExprs expressions (lowerEnv typingEnv.mod typingEnv.vars results) initial).2 :=
  typedStructExpressions (tyExprsAs_structExprs source) generated native extension allocated visible expressionChild

#print axioms typedStructExpressions
#print axioms typedExpressionsAs

end Goose.Lower.Validation.ReplacementContentFlowSource.SourceReadyExpressionListObservations
