import Goose.Lower.Validation.ReplacementScopedOperandsControlStatements

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem rhsOperands_assignOp (floor : Nat) (loop : Option LoopCtx) (operator : BinOp)
    (place : Place) (expr : Expr) (origin : OriginId)
    (placeChild : RhsOperandsRun floor (lowerPlace place)) (exprChild : RhsOperandsRun floor (lowerExpr expr)) :
    RhsOperandsRun floor (lowerStmt loop (.assignOp operator place expr origin)) := by
  intro env before bound
  simp only [lowerStmt]
  apply RhsOperandsAt.bindFresh bound (placeChild env before bound)
    (advB_lowerPlace place) (freshValue_lowerPlace place)
  intro address addressed _ addressedBound addressFresh
  apply RhsOperandsAt.bindFresh addressedBound
    (RhsOperandsAt.emitDef _ _ _ _ (by simpa only [Op.uses, List.mem_singleton] using
      fun live value equal => equal ▸ addressFresh live))
    (advB_emitDef _) (freshValue_emitDef _)
  intro old loaded loadRun loadedBound oldFresh
  have addressLoaded := addressFresh.after (dead_emitDef _) loadRun
  apply RhsOperandsAt.bindFresh loadedBound (exprChild env loaded loadedBound)
    (advB_lowerExpr expr) (freshValue_lowerExpr expr)
  intro rhs evaluated rhsRun evaluatedBound rhsFresh
  have addressEvaluated := addressLoaded.after (dead_lowerExpr expr) rhsRun
  have oldEvaluated := oldFresh.after (dead_lowerExpr expr) rhsRun
  apply RhsOperandsAt.bindUnchanged (fun _ _ => intTyOf_eq rfl)
  intro type
  apply RhsOperandsAt.bindFresh evaluatedBound
    (RhsOperandsAt.emitDef floor env evaluated (.bin operator type old rhs (some origin)) ?_)
    (advB_emitDef _) (freshValue_emitDef _)
  · intro result after resultRun _ resultFresh
    have addressAfter := addressEvaluated.after (dead_emitDef _) resultRun
    apply RhsOperandsAt.emitEffect
    intro live value member
    simp only [Effect.uses, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact addressAfter live
    · exact resultFresh live
  · intro live value member
    simp only [Op.uses, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact oldEvaluated live
    · exact rhsFresh live

theorem rhsOperands_assignWhole (floor : Nat) (loop : Option LoopCtx)
    (place : Place) (expr : Expr) (origin : OriginId)
    (placeChild : RhsOperandsRun floor (lowerPlace place)) (exprChild : RhsOperandsRun floor (lowerExpr expr)) :
    RhsOperandsRun floor (lowerStmt loop (.assignWhole place expr origin)) := by
  intro env before bound
  simp only [lowerStmt]
  apply RhsOperandsAt.bindFresh bound (placeChild env before bound)
    (advB_lowerPlace place) (freshValue_lowerPlace place)
  intro address addressed _ addressedBound addressFresh
  apply RhsOperandsAt.bindRun
    (RhsOperandsAt.emitEffect floor env addressed (.clear address (some origin)) ?_)
  · intro result cleared clearRun
    have clearBound := Nat.le_trans addressedBound (advB_emitEffect _ env addressed result cleared clearRun).vals
    have addressCleared := addressFresh.after (dead_emitEffect _) clearRun
    apply RhsOperandsAt.bindFresh clearBound (exprChild env cleared clearBound)
      (advB_lowerExpr expr) (freshValue_lowerExpr expr)
    intro value ended valueRun _ valueFresh
    have addressEnded := addressCleared.after (dead_lowerExpr expr) valueRun
    apply RhsOperandsAt.emitEffect
    intro live used member
    simp only [Effect.uses, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact addressEnded live
    · exact valueFresh live
  · simpa only [Effect.uses, List.mem_singleton] using
      fun live value equal => equal ▸ addressFresh live

theorem rhsOperands_resize (floor : Nat) (loop : Option LoopCtx) (place : Place)
    (size : Expr) (fill : Option Expr) (origin : OriginId)
    (placeChild : RhsOperandsRun floor (lowerPlace place))
    (sizeChild : RhsOperandsRun floor (lowerExpr size))
    (fillChild : ∀ expr, fill = some expr → RhsOperandsRun floor (lowerExpr expr)) :
    RhsOperandsRun floor (lowerStmt loop (.resize place size fill origin)) := by
  cases fill with
  | none =>
    intro env before bound
    simp only [lowerStmt]
    apply RhsOperandsAt.bindFresh bound (placeChild env before bound)
      (advB_lowerPlace place) (freshValue_lowerPlace place)
    intro address addressed _ addressedBound addressFresh
    apply RhsOperandsAt.bindFresh addressedBound (sizeChild env addressed addressedBound)
      (advB_lowerExpr size) (freshValue_lowerExpr size)
    intro length measured lengthRun measuredBound lengthFresh
    have addressMeasured := addressFresh.after (dead_lowerExpr size) lengthRun
    apply (RhsOperandsAt.pure _ _ _ _).bind
    apply RhsOperandsAt.emitEffect
    intro live value member
    simp only [pure_run, Effect.uses, Option.toList_none, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact addressMeasured live
    · exact lengthFresh live
  | some expression =>
    intro env before bound
    simp only [lowerStmt]
    apply RhsOperandsAt.bindFresh bound (placeChild env before bound)
      (advB_lowerPlace place) (freshValue_lowerPlace place)
    intro address addressed _ addressedBound addressFresh
    apply RhsOperandsAt.bindFresh addressedBound (sizeChild env addressed addressedBound)
      (advB_lowerExpr size) (freshValue_lowerExpr size)
    intro length measured lengthRun measuredBound lengthFresh
    have addressMeasured := addressFresh.after (dead_lowerExpr size) lengthRun
    apply RhsOperandsAt.bindFresh measuredBound (fillChild expression rfl env measured measuredBound)
      (advB_lowerExpr expression) (freshValue_lowerExpr expression)
    intro value filled fillRun _ valueFresh
    have addressFilled := addressMeasured.after (dead_lowerExpr expression) fillRun
    have lengthFilled := lengthFresh.after (dead_lowerExpr expression) fillRun
    apply (RhsOperandsAt.pure _ _ _ _).bind
    apply RhsOperandsAt.emitEffect
    intro live used member
    simp only [pure_run, Effect.uses, Option.toList_some, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with (rfl | rfl) | rfl
    · exact addressFilled live
    · exact lengthFilled live
    · exact valueFresh live

end Goose.Lower.Validation
