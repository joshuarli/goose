import Goose.Lower.Validation.ReplacementContentFlowSourceReadyLeaves
import Goose.Lower.Validation.DeadFrontier

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {callees : Array State} {func : Func}
  {types : Array (Option VTy)} {state : State} {completed before middle after : LS}
  {env : LEnv} {value child : ValueId}

theorem SourceReadyFrame.unary (frame : SourceReadyFrame module callees func types state completed)
    {operation : UnOp} {expression : Expr} {origin : OriginId}
    (childRun : lowerExpr expression env before = (child, middle))
    (run : lowerExpr (.un operation expression origin) env before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound middle)
    (childReady : EmitsOnly (ReadyOperands state) before middle ∧
      (middle.cur.isSome = true → flowAt state.values child ≠ .pending)) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  let integer := (intTyOf child env middle).1
  have integerRun : intTyOf child env middle = (integer, middle) :=
    Prod.ext rfl (intTyOf_state child env middle)
  have emitted : Lower.emitDef (.un operation integer child (some origin)) env middle = (value, after) := by
    simpa only [lowerExpr, bind_run, childRun, integerRun] using run
  obtain ⟨tail, ready⟩ := frame.emitDef emitted extension allocated bounded
    (by intro live operand member; have same : operand = child := by simpa [Op.uses] using member
        subst operand; exact childReady.2 live)
    (by intro _ address impossible; cases impossible) (by intro _ fn args org impossible; cases impossible)
  exact ⟨childReady.1.trans tail, ready⟩

theorem SourceReadyFrame.binary (frame : SourceReadyFrame module callees func types state completed)
    {operation : BinOp} {left right : Expr} {origin : OriginId} {leftValue rightValue : ValueId} {first : LS}
    (leftRun : lowerExpr left env before = (leftValue, first))
    (rightRun : lowerExpr right env first = (rightValue, middle))
    (run : lowerExpr (.bin operation left right origin) env before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound middle)
    (leftReady : EmitsOnly (ReadyOperands state) before first ∧
      (first.cur.isSome = true → flowAt state.values leftValue ≠ .pending))
    (rightReady : EmitsOnly (ReadyOperands state) first middle ∧
      (middle.cur.isSome = true → flowAt state.values rightValue ≠ .pending)) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  let integer := (intTyOf leftValue env middle).1
  have integerRun : intTyOf leftValue env middle = (integer, middle) :=
    Prod.ext rfl (intTyOf_state leftValue env middle)
  have emitted : Lower.emitDef (.bin operation integer leftValue rightValue (some origin)) env middle = (value, after) := by
    simpa only [lowerExpr, bind_run, leftRun, rightRun, integerRun] using run
  obtain ⟨tail, ready⟩ := frame.emitDef emitted extension allocated bounded
    (by
      intro live operand member
      have firstLive := (dead_lowerExpr right).live_before rightRun live
      rcases (show operand = leftValue ∨ operand = rightValue from by simpa [Op.uses] using member) with same | same
      · subst operand; exact leftReady.2 firstLive
      · subst operand; exact rightReady.2 live)
    (by intro _ address impossible; cases impossible) (by intro _ fn args org impossible; cases impossible)
  exact ⟨leftReady.1.trans (rightReady.1.trans tail), ready⟩

theorem SourceReadyFrame.conversion (frame : SourceReadyFrame module callees func types state completed)
    {kind : ConvKind} {target : Ty} {expression : Expr} {origin : OriginId}
    (childRun : lowerExpr expression env before = (child, middle))
    (run : lowerExpr (.conv kind target expression origin) env before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound middle)
    (childReady : EmitsOnly (ReadyOperands state) before middle ∧
      (middle.cur.isSome = true → flowAt state.values child ≠ .pending)) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  let source := (intTyOf child env middle).1
  have sourceRun : intTyOf child env middle = (source, middle) :=
    Prod.ext rfl (intTyOf_state child env middle)
  let destination := match target with | .int integer => integer | _ => source
  have emitted : Lower.emitDef (.conv kind source destination child (some origin)) env middle = (value, after) := by
    cases target <;> simpa only [lowerExpr, bind_run, childRun, sourceRun, destination] using run
  obtain ⟨tail, ready⟩ := frame.emitDef emitted extension allocated bounded
    (by intro live operand member; have same : operand = child := by simpa [Op.uses] using member
        subst operand; exact childReady.2 live)
    (by intro _ address impossible; cases impossible) (by intro _ fn args org impossible; cases impossible)
  exact ⟨childReady.1.trans tail, ready⟩

theorem SourceReadyFrame.comparison (frame : SourceReadyFrame module callees func types state completed)
    {operation : CmpOp} {left right : Expr} {leftValue rightValue : ValueId} {first : LS}
    (leftRun : lowerExpr left env before = (leftValue, first))
    (rightRun : lowerExpr right env first = (rightValue, middle))
    (run : lowerExpr (.cmp operation left right) env before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound middle)
    (leftReady : EmitsOnly (ReadyOperands state) before first ∧
      (first.cur.isSome = true → flowAt state.values leftValue ≠ .pending))
    (rightReady : EmitsOnly (ReadyOperands state) first middle ∧
      (middle.cur.isSome = true → flowAt state.values rightValue ≠ .pending)) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  let operandType := (valTy leftValue env middle).1
  have classification : valTy leftValue env middle = (operandType, middle) :=
    Prod.ext rfl (valTy_eq rfl)
  have operands : ∀ live : middle.cur.isSome = true, ∀ operand,
      operand = leftValue ∨ operand = rightValue → flowAt state.values operand ≠ .pending := by
    intro live operand member
    rcases member with same | same
    · subst operand; exact leftReady.2 ((dead_lowerExpr right).live_before rightRun live)
    · subst operand; exact rightReady.2 live
  simp only [lowerExpr, bind_run, leftRun, rightRun, classification] at run
  generalize selected : operandType = actualType at run
  split at run
  · obtain ⟨tail, result⟩ := frame.emitDef run extension allocated bounded
      (by intro live operand member; exact operands live operand (by simpa [Op.uses] using member))
      (by intro _ address impossible; cases impossible) (by intro _ fn args org impossible; cases impossible)
    exact ⟨leftReady.1.trans (rightReady.1.trans tail), result⟩
  · obtain ⟨tail, result⟩ := frame.emitDef run extension allocated bounded
      (by intro live operand member; exact operands live operand (by simpa [Op.uses] using member))
      (by intro _ address impossible; cases impossible) (by intro _ fn args org impossible; cases impossible)
    exact ⟨leftReady.1.trans (rightReady.1.trans tail), result⟩

#print axioms SourceReadyFrame.comparison

#print axioms SourceReadyFrame.conversion

#print axioms SourceReadyFrame.unary
#print axioms SourceReadyFrame.binary

end Goose.Lower.Validation.ReplacementContentFlowSource
