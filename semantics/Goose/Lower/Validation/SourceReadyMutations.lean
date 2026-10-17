import Goose.Lower.Validation.SourceReadyControl

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem ready_expressionStatement {state : State} {env : LEnv} {before : LS}
    {loop : Option LoopCtx} {expression : Expr} {origin : OriginId}
    (child : ValueReadyAt state (lowerExpr expression) env before) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.expr expression origin) env before).2 := child.1

theorem ready_clear {state : State} {env : LEnv} {before : LS}
    {loop : Option LoopCtx} {owner : Place} {origin : OriginId}
    (child : ValueReadyAt state (lowerPlace owner) env before) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.clear owner origin) env before).2 := by
  let lowered := lowerPlace owner env before
  have emitted : EmitsOnly (ReadyOperands state) lowered.2
      (emitEffect (.clear lowered.1 (some origin)) env lowered.2).2 := ready_emitEffect rfl (by
    intro live operand member
    have same : operand = lowered.1 := by simpa [Inst.uses, Effect.uses] using member
    subst operand
    exact child.2 live)
  exact child.1.trans emitted

theorem ready_append {state : State} {env : LEnv} {before : LS}
    {loop : Option LoopCtx} {owner : Place} {source : View} {origin : OriginId}
    (place : ValueReadyAt state (lowerPlace owner) env before)
    (view : ValueReadyAt state (lowerView source) env (lowerPlace owner env before).2) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.append owner source origin) env before).2 := by
  let address := lowerPlace owner env before
  let content := lowerView source env address.2
  have emitted : EmitsOnly (ReadyOperands state) content.2
      (emitEffect (.append address.1 content.1 (some origin)) env content.2).2 := ready_emitEffect rfl (by
    intro live operand member
    rcases (show operand = address.1 ∨ operand = content.1 from by simpa [Inst.uses, Effect.uses] using member) with same | same
    · subst operand
      exact place.2 ((dead_lowerView source).live_before rfl live)
    · subst operand
      exact view.2 live)
  exact place.1.trans (view.1.trans emitted)

theorem ready_popN {state : State} {env : LEnv} {before : LS}
    {loop : Option LoopCtx} {owner : Place} {count : Expr} {origin : OriginId}
    (place : ValueReadyAt state (lowerPlace owner) env before)
    (number : ValueReadyAt state (lowerExpr count) env (lowerPlace owner env before).2) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.popN owner count origin) env before).2 := by
  let address := lowerPlace owner env before
  let content := lowerExpr count env address.2
  have emitted : EmitsOnly (ReadyOperands state) content.2
      (emitEffect (.popN address.1 content.1 (some origin)) env content.2).2 := ready_emitEffect rfl (by
    intro live operand member
    rcases (show operand = address.1 ∨ operand = content.1 from by simpa [Inst.uses, Effect.uses] using member) with same | same
    · subst operand
      exact place.2 ((dead_lowerExpr count).live_before rfl live)
    · subst operand
      exact number.2 live)
  exact place.1.trans (number.1.trans emitted)

theorem ready_resize_none {state : State} {env : LEnv} {before : LS}
    {loop : Option LoopCtx} {owner : Place} {size : Expr} {origin : OriginId}
    (place : ValueReadyAt state (lowerPlace owner) env before)
    (number : ValueReadyAt state (lowerExpr size) env (lowerPlace owner env before).2) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.resize owner size none origin) env before).2 := by
  let address := lowerPlace owner env before
  let content := lowerExpr size env address.2
  have emitted : EmitsOnly (ReadyOperands state) content.2
      (emitEffect (.resize address.1 content.1 none (some origin)) env content.2).2 := ready_emitEffect rfl (by
    intro live operand member
    rcases (show operand = address.1 ∨ operand = content.1 from by simpa [Inst.uses, Effect.uses] using member) with same | same
    · subst operand
      exact place.2 ((dead_lowerExpr size).live_before rfl live)
    · subst operand
      exact number.2 live)
  exact place.1.trans (number.1.trans emitted)

theorem ready_resize_some {state : State} {env : LEnv} {before : LS}
    {loop : Option LoopCtx} {owner : Place} {size fill : Expr} {origin : OriginId}
    (place : ValueReadyAt state (lowerPlace owner) env before)
    (number : ValueReadyAt state (lowerExpr size) env (lowerPlace owner env before).2)
    (initial : ValueReadyAt state (lowerExpr fill) env (lowerExpr size env (lowerPlace owner env before).2).2) :
    EmitsOnly (ReadyOperands state) before (lowerStmt loop (.resize owner size (some fill) origin) env before).2 := by
  let address := lowerPlace owner env before
  let count := lowerExpr size env address.2
  let content := lowerExpr fill env count.2
  have emitted : EmitsOnly (ReadyOperands state) content.2
      (emitEffect (.resize address.1 count.1 (some content.1) (some origin)) env content.2).2 := ready_emitEffect rfl (by
    intro live operand member
    have countLive := (dead_lowerExpr fill).live_before (show lowerExpr fill env count.2 = content from rfl) live
    rcases (show operand = address.1 ∨ operand = count.1 ∨ operand = content.1 from by
      simpa [Inst.uses, Effect.uses] using member) with same | same | same
    · subst operand
      exact place.2 ((dead_lowerExpr size).live_before rfl countLive)
    · subst operand
      exact number.2 countLive
    · subst operand
      exact initial.2 live)
  exact place.1.trans (number.1.trans (initial.1.trans emitted))

#print axioms ready_expressionStatement
#print axioms ready_clear
#print axioms ready_append
#print axioms ready_popN
#print axioms ready_resize_none
#print axioms ready_resize_some

end Goose.Lower.Validation.ReplacementContentFlowSource
