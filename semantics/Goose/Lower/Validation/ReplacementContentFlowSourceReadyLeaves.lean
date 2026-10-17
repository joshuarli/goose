import Goose.Lower.Validation.ReplacementContentFlowSourceReadyEmit

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {callees : Array State} {func : Func}
  {types : Array (Option VTy)} {state : State} {completed before after : LS}
  {env : LEnv} {value : ValueId}

theorem SourceReadyFrame.literal (frame : SourceReadyFrame module callees func types state completed)
    {integerType : IntTy} {number : Int}
    (run : lowerExpr (.lit integerType number) env before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound before) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  exact frame.emitDef run extension allocated bounded (by simp [Op.uses])
    (by intro _ address impossible; cases impossible) (by intro _ fn args origin impossible; cases impossible)

theorem SourceReadyFrame.boolean (frame : SourceReadyFrame module callees func types state completed)
    {boolean : Bool}
    (run : lowerExpr (.bool boolean) env before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound before) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  exact frame.emitDef run extension allocated bounded (by simp [Op.uses])
    (by intro _ address impossible; cases impossible) (by intro _ fn args origin impossible; cases impossible)

theorem SourceReadyFrame.variablePlace (frame : SourceReadyFrame module callees func types state completed)
    {variableId : VarId}
    (run : lowerPlace (.var variableId) env before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound before) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  exact frame.emitDef run extension allocated bounded (by simp [Op.uses])
    (by intro _ address impossible; cases impossible) (by intro _ fn args origin impossible; cases impossible)

theorem SourceReadyFrame.globalPlace (frame : SourceReadyFrame module callees func types state completed)
    {globalId : GlobalId}
    (run : lowerPlace (.global globalId) env before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound before) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  exact frame.emitDef run extension allocated bounded (by simp [Op.uses])
    (by intro _ address impossible; cases impossible) (by intro _ fn args origin impossible; cases impossible)

theorem SourceReadyFrame.not (frame : SourceReadyFrame module callees func types state completed)
    {expression : Expr}
    (run : lowerExpr (.not expression) env before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound (lowerExpr expression env before).2)
    (child : EmitsOnly (ReadyOperands state) before (lowerExpr expression env before).2 ∧
      ((lowerExpr expression env before).2.cur.isSome = true →
        flowAt state.values (lowerExpr expression env before).1 ≠ .pending)) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  have emitted : Lower.emitDef (.boolNot (lowerExpr expression env before).1) env
      (lowerExpr expression env before).2 = (value, after) := by
    simpa only [lowerExpr, bind_run] using run
  obtain ⟨tail, result⟩ := frame.emitDef emitted extension allocated bounded
    (by intro live operand member; have same : operand = (lowerExpr expression env before).1 := by simpa [Op.uses] using member
        subst operand; exact child.2 live)
    (by intro _ address impossible; cases impossible) (by intro _ fn args origin impossible; cases impossible)
  exact ⟨child.1.trans tail, result⟩

#print axioms SourceReadyFrame.literal
#print axioms SourceReadyFrame.boolean
#print axioms SourceReadyFrame.variablePlace
#print axioms SourceReadyFrame.globalPlace
#print axioms SourceReadyFrame.not

end Goose.Lower.Validation.ReplacementContentFlowSource
