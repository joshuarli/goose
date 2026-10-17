import Goose.Lower.Validation.SourceReadyTypedStatementsGenerated

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {callees : Array State} {func : Func}
  {types : Array (Option VTy)} {state : State} {completed before : LS}
  {typingEnv output : TEnv} {results : List Ty} {loop : Option LoopCtx}
  {scope start finish : Nat} {origin : OriginId}

theorem typed_ready_expression {expression : Expr}
    (source : Core.tyStmt typingEnv scope (.expr expression origin) start = .ok (output, finish))
    (visible : VisibleSlotsReady typingEnv state)
    (child : ∀ type, Core.tyExpr typingEnv expression start = .ok (type, finish) →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) before) :
    EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.expr expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.expr expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state) := by
  obtain ⟨type, checked, rfl⟩ := tyStmt_expr_children source
  exact ⟨ready_expressionStatement (loop := loop) (child type checked), fun _ => visible⟩

theorem typed_ready_assert {expression : Expr}
    (source : Core.tyStmt typingEnv scope (.assertS expression origin) start = .ok (output, finish))
    (visible : VisibleSlotsReady typingEnv state)
    (child : Core.tyExpr typingEnv expression start = .ok (.bool, finish) →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) before) :
    EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.assertS expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.assertS expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state) := by
  obtain ⟨checked, rfl⟩ := tyStmt_assert_children source
  exact ⟨ready_assert (loop := loop) (child checked), fun _ => visible⟩

theorem typed_ready_exit {expression : Expr}
    (source : Core.tyStmt typingEnv scope (.exit expression origin) start = .ok (output, finish))
    (visible : VisibleSlotsReady typingEnv state)
    (child : ∀ integer, Core.tyExpr typingEnv expression start = .ok (.int integer, finish) →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) before) :
    EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.exit expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.exit expression origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state) := by
  obtain ⟨integer, checked, rfl⟩ := tyStmt_exit_children source
  exact ⟨ready_exit (loop := loop) (child integer checked), fun _ => visible⟩

theorem typed_ready_abort {message : String}
    (source : Core.tyStmt typingEnv scope (.abort message origin) start = .ok (output, finish))
    (visible : VisibleSlotsReady typingEnv state) :
    EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.abort message origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.abort message origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state) := by
  have outputEq := (tyStmt_abort_facts source).1
  subst output
  exact ⟨ready_abort (loop := loop), fun _ => visible⟩

theorem typed_ready_break
    (source : Core.tyStmt typingEnv scope (.brk origin) start = .ok (output, finish))
    (visible : VisibleSlotsReady typingEnv state) :
    EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.brk origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.brk origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state) := by
  have outputEq := (tyStmt_break_facts source).2.1
  subst output
  exact ⟨ready_break (loop := loop), fun _ => visible⟩

theorem typed_ready_return_none
    (source : Core.tyStmt typingEnv scope (.ret none origin) start = .ok (output, finish))
    (visible : VisibleSlotsReady typingEnv state) :
    EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.ret none origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.ret none origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state) := by
  have outputEq := (tyStmt_returnUnit_facts source).2.2.1
  subst output
  exact ⟨ready_return_none (loop := loop), fun _ => visible⟩

theorem SourceReadyFrame.typedReturnSome {expression : Expr}
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyStmt typingEnv scope (.ret (some expression) origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before)
    (extension : (lowerStmt loop (.ret (some expression) origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.ret (some expression) origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (child : ∀ type, Core.tyExpr typingEnv expression start = .ok (type, finish) →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) before) :
    EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.ret (some expression) origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.ret (some expression) origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state) := by
  obtain ⟨expected, actual, impl, _, _, _, checked, _, outputEq⟩ := tyStmt_return_children source
  subst output
  exact ⟨frame.return_some (loop := loop) extension allocated (generated.lowerExpr expression rfl).live
    (child actual checked), fun _ => visible⟩

theorem SourceReadyFrame.typedContinue
    (frame : SourceReadyFrame module callees func types state completed)
    (source : Core.tyStmt typingEnv scope (.cont origin) start = .ok (output, finish))
    (generated : GeneratedBuilderState before)
    (extension : (lowerStmt loop (.cont origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed)
    (allocated : (lowerStmt loop (.cont origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (counter : ∀ context, loop = some context → ∀ header integerType index,
      context.cont = .next header integerType index → before.cur.isSome = true →
        flowAt state.values index ≠ .pending) :
    EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.cont origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.cont origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state) := by
  have outputEq := (tyStmt_continue_facts source).2.1
  subst output
  exact ⟨frame.continue (loop := loop) extension allocated generated.live counter, fun _ => visible⟩

end Goose.Lower.Validation.ReplacementContentFlowSource
