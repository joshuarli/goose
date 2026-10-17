import Goose.Lower.Validation.SourceReadyMutations

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.rebind {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS} {env : LEnv}
    {loop : Option LoopCtx} {slot : SlotId} {expression : Expr} {origin : OriginId}
    (frame : SourceReadyFrame module callees func types state completed)
    (extension : (lowerStmt loop (.rebind slot expression origin) env before).2.Ext completed)
    (allocated : (lowerStmt loop (.rebind slot expression origin) env before).2.vals.size ≤ completed.vals.size)
    (bounded : LiveBound (lowerExpr expression env before).2)
    (child : ValueReadyAt state (lowerExpr expression) env before) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.rebind slot expression origin) env before).2 := by
  let evaluated := lowerExpr expression env before
  let coerced := Lower.coerceSlot slot evaluated.1 origin env evaluated.2
  let address := Lower.emitDef (.slotAddr slot) env coerced.2
  let stored := (emitEffect (.store address.1 coerced.1 (some origin)) env address.2).2
  have storeAdvance : address.2.Adv stored := adv_emitEffect rfl
  have addressAdvance : coerced.2.Adv address.2 := adv_emitDef rfl
  have coerceExtension : coerced.2.Ext completed := addressAdvance.ext.trans (storeAdvance.ext.trans extension)
  have coerceAllocated : coerced.2.vals.size ≤ completed.vals.size :=
    Nat.le_trans addressAdvance.vals (Nat.le_trans storeAdvance.vals allocated)
  have coerceReady := frame.coerceSlot (show Lower.coerceSlot slot evaluated.1 origin env evaluated.2 = coerced from rfl)
    coerceExtension coerceAllocated bounded child.2
  have coerceAdvance : evaluated.2.Adv coerced.2 := advB_coerceSlot slot evaluated.1 origin env evaluated.2 _ _ rfl
  have addressReady := frame.emitDef (show Lower.emitDef (.slotAddr slot) env coerced.2 = address from rfl)
    (storeAdvance.ext.trans extension) (Nat.le_trans storeAdvance.vals allocated)
    (liveBound_of_adv coerceAdvance bounded) (by intro _ operand member; simp [Op.uses] at member)
    (by intro _ value impossible; cases impossible) (by intro _ fn args org impossible; cases impossible)
  have storeReady : EmitsOnly (ReadyOperands state) address.2 stored := ready_emitEffect rfl (by
    intro live operand member
    rcases (show operand = address.1 ∨ operand = coerced.1 from by simpa [Inst.uses, Effect.uses] using member) with same | same
    · subst operand; exact addressReady.2 live
    · subst operand; exact coerceReady.2 ((dead_emitDef _).live_before rfl live))
  exact child.1.trans (coerceReady.1.trans (addressReady.1.trans storeReady))

theorem SourceReadyFrame.assignOp {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS} {env : LEnv}
    {loop : Option LoopCtx} {operation : BinOp} {place : Place} {expression : Expr} {origin : OriginId}
    (frame : SourceReadyFrame module callees func types state completed)
    (extension : (lowerStmt loop (.assignOp operation place expression origin) env before).2.Ext completed)
    (allocated : (lowerStmt loop (.assignOp operation place expression origin) env before).2.vals.size ≤ completed.vals.size)
    (bounded : LiveBound (lowerPlace place env before).2)
    (scalar : (lowerPlace place env before).2.cur.isSome = true →
      valRefLike types (lowerPlace place env before).2.vals.size = false)
    (addressReady : ValueReadyAt state (lowerPlace place) env before)
    (child :
      let address := lowerPlace place env before
      let loaded := Lower.emitDef (.load address.1) env address.2
      ValueReadyAt state (lowerExpr expression) env loaded.2) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.assignOp operation place expression origin) env before).2 := by
  let address := lowerPlace place env before
  let loaded := Lower.emitDef (.load address.1) env address.2
  let evaluated := lowerExpr expression env loaded.2
  let integerType := (intTyOf loaded.1 env evaluated.2).1
  let combined := Lower.emitDef (.bin operation integerType loaded.1 evaluated.1 (some origin)) env evaluated.2
  let stored := (emitEffect (.store address.1 combined.1 (some origin)) env combined.2).2
  have classifyState : (intTyOf loaded.1 env evaluated.2).2 = evaluated.2 := intTyOf_eq rfl
  have finalState : (lowerStmt loop (.assignOp operation place expression origin) env before).2 = stored := by
    simp only [lowerStmt, bind_run]
    change (emitEffect (.store address.1
      (Lower.emitDef (.bin operation integerType loaded.1 evaluated.1 (some origin)) env
        (intTyOf loaded.1 env evaluated.2).2).1 (some origin)) env
      (Lower.emitDef (.bin operation integerType loaded.1 evaluated.1 (some origin)) env
        (intTyOf loaded.1 env evaluated.2).2).2).2 = stored
    rw [classifyState]
  rw [finalState] at extension allocated ⊢
  have storeAdvance : combined.2.Adv stored := adv_emitEffect rfl
  have combineAdvance : evaluated.2.Adv combined.2 := adv_emitDef rfl
  have childAdvance : loaded.2.Adv evaluated.2 := advB_lowerExpr expression env loaded.2 _ _ rfl
  have loadAdvance : address.2.Adv loaded.2 := adv_emitDef rfl
  have loadReady := frame.emitDef (show Lower.emitDef (.load address.1) env address.2 = loaded from rfl)
    (childAdvance.ext.trans (combineAdvance.ext.trans (storeAdvance.ext.trans extension)))
    (Nat.le_trans childAdvance.vals (Nat.le_trans combineAdvance.vals (Nat.le_trans storeAdvance.vals allocated)))
    bounded (by
      intro live operand member
      have same : operand = address.1 := by simpa [Op.uses] using member
      subst operand
      exact addressReady.2 live)
    (by intro live value same reference; rw [scalar live] at reference; contradiction)
    (by intro _ fn args org impossible; cases impossible)
  have combinedReady := frame.emitDef (show Lower.emitDef (.bin operation integerType loaded.1 evaluated.1 (some origin))
      env evaluated.2 = combined from rfl)
    (storeAdvance.ext.trans extension) (Nat.le_trans storeAdvance.vals allocated)
    (liveBound_of_adv childAdvance (liveBound_of_adv loadAdvance bounded)) (by
      intro live operand member
      rcases (show operand = loaded.1 ∨ operand = evaluated.1 from by simpa [Op.uses] using member) with same | same
      · subst operand; exact loadReady.2 ((dead_lowerExpr expression).live_before rfl live)
      · subst operand; exact child.2 live)
    (by intro _ value impossible; cases impossible) (by intro _ fn args org impossible; cases impossible)
  have storeReady : EmitsOnly (ReadyOperands state) combined.2 stored := ready_emitEffect rfl (by
    intro live operand member
    have evaluatedLive := (dead_emitDef _).live_before (show Lower.emitDef
      (.bin operation integerType loaded.1 evaluated.1 (some origin)) env evaluated.2 = combined from rfl) live
    rcases (show operand = address.1 ∨ operand = combined.1 from by simpa [Inst.uses, Effect.uses] using member) with same | same
    · subst operand
      exact addressReady.2 ((dead_emitDef _).live_before rfl
        ((dead_lowerExpr expression).live_before rfl evaluatedLive))
    · subst operand; exact combinedReady.2 live)
  exact addressReady.1.trans (loadReady.1.trans (child.1.trans (combinedReady.1.trans storeReady)))

#print axioms SourceReadyFrame.rebind
#print axioms SourceReadyFrame.assignOp

end Goose.Lower.Validation.ReplacementContentFlowSource
