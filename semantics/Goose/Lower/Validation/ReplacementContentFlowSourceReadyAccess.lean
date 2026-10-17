import Goose.Lower.Validation.ReplacementContentFlowSourceReadyLeaves
import Goose.Lower.Validation.DeadFrontier

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {callees : Array State} {func : Func}
  {types : Array (Option VTy)} {state : State} {completed before middle after : LS}
  {env : LEnv} {value input : ValueId}

theorem SourceReadyFrame.field (frame : SourceReadyFrame module callees func types state completed)
    {owner : Place} {index : Nat}
    (childRun : lowerPlace owner env before = (input, middle))
    (run : lowerPlace (.field owner index) env before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound middle)
    (child : EmitsOnly (ReadyOperands state) before middle ∧
      (middle.cur.isSome = true → flowAt state.values input ≠ .pending)) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  have emitted : Lower.emitDef (.fieldAddr input index) env middle = (value, after) := by
    simpa only [lowerPlace, bind_run, childRun] using run
  obtain ⟨tail, result⟩ := frame.emitDef emitted extension allocated bounded
    (by intro live operand member; have same : operand = input := by simpa [Op.uses] using member
        subst operand; exact child.2 live)
    (by intro _ address impossible; cases impossible) (by intro _ fn args origin impossible; cases impossible)
  exact ⟨child.1.trans tail, result⟩

theorem SourceReadyFrame.viewOf (frame : SourceReadyFrame module callees func types state completed)
    {place : Place}
    (childRun : lowerPlace place env before = (input, middle))
    (run : lowerView (.of place) env before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound middle)
    (child : EmitsOnly (ReadyOperands state) before middle ∧
      (middle.cur.isSome = true → flowAt state.values input ≠ .pending)) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  have emitted : Lower.emitDef (.snapshot (match place with | .var _ | .global _ => .owner | _ => .borrowed) input)
      env middle = (value, after) := by
    cases place <;> simpa only [lowerView, bind_run, childRun] using run
  obtain ⟨tail, result⟩ := frame.emitDef emitted extension allocated bounded
    (by intro live operand member; have same : operand = input := by simpa [Op.uses] using member
        subst operand; exact child.2 live)
    (by intro _ address impossible; cases impossible) (by intro _ fn args origin impossible; cases impossible)
  exact ⟨child.1.trans tail, result⟩

theorem SourceReadyFrame.viewValue (frame : SourceReadyFrame module callees func types state completed)
    {expression : Expr}
    (childRun : lowerExpr expression env before = (input, middle))
    (run : lowerView (.val expression) env before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound middle)
    (child : EmitsOnly (ReadyOperands state) before middle ∧
      (middle.cur.isSome = true → flowAt state.values input ≠ .pending)) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  have emitted : Lower.emitDef (.sliceView input) env middle = (value, after) := by
    simpa only [lowerView, bind_run, childRun] using run
  obtain ⟨tail, result⟩ := frame.emitDef emitted extension allocated bounded
    (by intro live operand member; have same : operand = input := by simpa [Op.uses] using member
        subst operand; exact child.2 live)
    (by intro _ address impossible; cases impossible) (by intro _ fn args origin impossible; cases impossible)
  exact ⟨child.1.trans tail, result⟩

theorem SourceReadyFrame.element (frame : SourceReadyFrame module callees func types state completed)
    {view : View} {index : Expr} {origin : OriginId} {viewValue indexValue : ValueId} {first : LS}
    (viewRun : lowerView view env before = (viewValue, first))
    (indexRun : lowerExpr index env first = (indexValue, middle))
    (run : lowerPlace (.elem view index origin) env before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound middle)
    (viewReady : EmitsOnly (ReadyOperands state) before first ∧
      (first.cur.isSome = true → flowAt state.values viewValue ≠ .pending))
    (indexReady : EmitsOnly (ReadyOperands state) first middle ∧
      (middle.cur.isSome = true → flowAt state.values indexValue ≠ .pending)) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  have emitted : Lower.emitDef (.indexChecked viewValue indexValue (some origin)) env middle = (value, after) := by
    simpa only [lowerPlace, bind_run, viewRun, indexRun] using run
  obtain ⟨tail, result⟩ := frame.emitDef emitted extension allocated bounded
    (by
      intro live operand member
      have firstLive := (dead_lowerExpr index).live_before indexRun live
      rcases (show operand = viewValue ∨ operand = indexValue from by simpa [Op.uses] using member) with same | same
      · subst operand; exact viewReady.2 firstLive
      · subst operand; exact indexReady.2 live)
    (by intro _ address impossible; cases impossible) (by intro _ fn args org impossible; cases impossible)
  exact ⟨viewReady.1.trans (indexReady.1.trans tail), result⟩

#print axioms SourceReadyFrame.field
#print axioms SourceReadyFrame.viewOf
#print axioms SourceReadyFrame.viewValue
#print axioms SourceReadyFrame.element

end Goose.Lower.Validation.ReplacementContentFlowSource
