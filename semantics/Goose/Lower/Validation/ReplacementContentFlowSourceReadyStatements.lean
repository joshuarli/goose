import Goose.Lower.Validation.ReplacementContentFlowSourceReadyCoercion
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyBindings
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyEffects
import Goose.Lower.Validation.DeadFrontier

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.letS {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before first after : LS}
    {env : LEnv} {typingEnv : TEnv} {slot : SlotId} {expression : Expr} {origin : OriginId}
    {child : ValueId} {loop : Option LoopCtx}
    (frame : SourceReadyFrame module callees func types state completed)
    (childRun : lowerExpr expression env before = (child, first))
    (run : lowerStmt loop (.letS slot expression origin) env before = ((), after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound first) (slotBound : slot < func.slots.size)
    (visible : VisibleSlotsReady typingEnv state)
    (childReady : EmitsOnly (ReadyOperands state) before first ∧
      (first.cur.isSome = true → flowAt state.values child ≠ .pending)) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → VisibleSlotsReady { typingEnv with visible := slot :: typingEnv.visible } state) := by
  simp only [lowerStmt] at run
  obtain ⟨actualChild, actualFirst, actualRun, tailRun⟩ := bind_eq.mp run
  rw [childRun] at actualRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj actualRun
  obtain ⟨coerced, middle, coerceRun, initRun⟩ := bind_eq.mp tailRun
  have tail := adv_emitEffect initRun
  obtain ⟨coerceEmits, coerceReady⟩ := frame.coerceSlot coerceRun (tail.ext.trans extension)
    (Nat.le_trans tail.vals allocated) bounded childReady.2
  have middleBound := liveBound_of_adv (advB_coerceSlot slot child origin _ _ _ _ coerceRun) bounded
  have initEmits := ready_emitEffect initRun (by
    intro live operand member
    have same : operand = coerced := by simpa [ReadyOperands, Inst.uses, Effect.uses] using member
    subst operand
    exact coerceReady live)
  refine ⟨childReady.1.trans (coerceEmits.trans initEmits), ?_⟩
  intro live
  have inputLive := (dead_emitEffect (.slotInit slot coerced (some origin))).live_before initRun live
  exact visible.declare (frame.slotInit initRun extension middleBound inputLive slotBound (coerceReady inputLive)).2

theorem ready_assign {state : State} {env : LEnv} {loop : Option LoopCtx}
    {place : Place} {expression : Expr} {origin : OriginId} {address value : ValueId}
    {before first middle after : LS}
    (placeRun : lowerPlace place env before = (address, first))
    (valueRun : lowerExpr expression env first = (value, middle))
    (run : lowerStmt loop (.assign place expression origin) env before = ((), after))
    (placeReady : EmitsOnly (ReadyOperands state) before first ∧
      (first.cur.isSome = true → flowAt state.values address ≠ .pending))
    (valueReady : EmitsOnly (ReadyOperands state) first middle ∧
      (middle.cur.isSome = true → flowAt state.values value ≠ .pending)) :
    EmitsOnly (ReadyOperands state) before after := by
  have emitted : emitEffect (.store address value (some origin)) env middle = ((), after) := by
    simpa only [lowerStmt, bind_run, placeRun, valueRun] using run
  apply placeReady.1.trans (valueReady.1.trans (ready_emitEffect emitted ?_))
  intro live operand member
  have firstLive := (dead_lowerExpr expression).live_before valueRun live
  rcases (show operand = address ∨ operand = value from by simpa [Inst.uses, Effect.uses] using member) with same | same
  · subst operand; exact placeReady.2 firstLive
  · subst operand; exact valueReady.2 live

theorem ready_assignWhole {state : State} {env : LEnv} {loop : Option LoopCtx}
    {place : Place} {expression : Expr} {origin : OriginId} {address value : ValueId}
    {before first cleared middle after : LS}
    (placeRun : lowerPlace place env before = (address, first))
    (clearRun : emitEffect (.clear address (some origin)) env first = ((), cleared))
    (valueRun : lowerExpr expression env cleared = (value, middle))
    (run : lowerStmt loop (.assignWhole place expression origin) env before = ((), after))
    (placeReady : EmitsOnly (ReadyOperands state) before first ∧
      (first.cur.isSome = true → flowAt state.values address ≠ .pending))
    (valueReady : EmitsOnly (ReadyOperands state) cleared middle ∧
      (middle.cur.isSome = true → flowAt state.values value ≠ .pending)) :
    EmitsOnly (ReadyOperands state) before after := by
  have clearEmitted := ready_emitEffect clearRun (by
    intro live operand member
    have same : operand = address := by simpa [Inst.uses, Effect.uses] using member
    subst operand; exact placeReady.2 live)
  have emitted : emitEffect (.replace address value (some origin)) env middle = ((), after) := by
    simpa only [lowerStmt, bind_run, placeRun, clearRun, valueRun] using run
  apply placeReady.1.trans (clearEmitted.trans (valueReady.1.trans (ready_emitEffect emitted ?_)))
  intro live operand member
  have clearedLive := (dead_lowerExpr expression).live_before valueRun live
  have firstLive := (dead_emitEffect (.clear address (some origin))).live_before clearRun clearedLive
  rcases (show operand = address ∨ operand = value from by simpa [Inst.uses, Effect.uses] using member) with same | same
  · subst operand; exact placeReady.2 firstLive
  · subst operand; exact valueReady.2 live

#print axioms SourceReadyFrame.letS
#print axioms ready_assign
#print axioms ready_assignWhole

end Goose.Lower.Validation.ReplacementContentFlowSource
