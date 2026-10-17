import Goose.Lower.Validation.ReplacementContentFlowSourceReadyLeaves

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {callees : Array State} {func : Func}
  {types : Array (Option VTy)} {state : State} {completed before middle after : LS}
  {env : LEnv} {value input : ValueId}

theorem SourceReadyFrame.length (frame : SourceReadyFrame module callees func types state completed)
    {view : View}
    (childRun : lowerView view env before = (input, middle))
    (run : lowerExpr (.len view) env before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound middle)
    (child : EmitsOnly (ReadyOperands state) before middle ∧
      (middle.cur.isSome = true → flowAt state.values input ≠ .pending)) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  have emitted : Lower.emitDef (.viewLen input) env middle = (value, after) := by
    simpa only [lowerExpr, bind_run, childRun] using run
  obtain ⟨tail, result⟩ := frame.emitDef emitted extension allocated bounded
    (by intro live operand member; have same : operand = input := by simpa [Op.uses] using member
        subst operand; exact child.2 live)
    (by intro _ address impossible; cases impossible) (by intro _ fn args origin impossible; cases impossible)
  exact ⟨child.1.trans tail, result⟩

theorem SourceReadyFrame.fill (frame : SourceReadyFrame module callees func types state completed)
    {elementType : Ty} {expression : Expr}
    (childRun : lowerExpr expression env before = (input, middle))
    (run : lowerExpr (.fill elementType expression) env before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound middle)
    (child : EmitsOnly (ReadyOperands state) before middle ∧
      (middle.cur.isSome = true → flowAt state.values input ≠ .pending)) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  have emitted : Lower.emitDef (.arrFill elementType input) env middle = (value, after) := by
    simpa only [lowerExpr, bind_run, childRun] using run
  obtain ⟨tail, result⟩ := frame.emitDef emitted extension allocated bounded
    (by intro live operand member; have same : operand = input := by simpa [Op.uses] using member
        subst operand; exact child.2 live)
    (by intro _ address impossible; cases impossible) (by intro _ fn args origin impossible; cases impossible)
  exact ⟨child.1.trans tail, result⟩

theorem SourceReadyFrame.pop (frame : SourceReadyFrame module callees func types state completed)
    {owner : Place} {origin : OriginId}
    (childRun : lowerPlace owner env before = (input, middle))
    (run : lowerExpr (.pop owner origin) env before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound middle)
    (child : EmitsOnly (ReadyOperands state) before middle ∧
      (middle.cur.isSome = true → flowAt state.values input ≠ .pending)) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  have emitted : Lower.emitDef (.pop input (some origin)) env middle = (value, after) := by
    simpa only [lowerExpr, bind_run, childRun] using run
  obtain ⟨tail, result⟩ := frame.emitDef emitted extension allocated bounded
    (by intro live operand member; have same : operand = input := by simpa [Op.uses] using member
        subst operand; exact child.2 live)
    (by intro _ address impossible; cases impossible) (by intro _ fn args origin impossible; cases impossible)
  exact ⟨child.1.trans tail, result⟩

theorem SourceReadyFrame.array (frame : SourceReadyFrame module callees func types state completed)
    {elementType : Ty} {expressions : List Expr} {inputs : List ValueId}
    (childrenRun : lowerExprs expressions env before = (inputs, middle))
    (run : lowerExpr (.arrLit elementType expressions) env before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound middle)
    (children : EmitsOnly (ReadyOperands state) before middle ∧
      (middle.cur.isSome = true → ∀ input ∈ inputs, flowAt state.values input ≠ .pending)) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  have emitted : Lower.emitDef (.arrLit elementType inputs) env middle = (value, after) := by
    simpa only [lowerExpr, bind_run, childrenRun] using run
  obtain ⟨tail, result⟩ := frame.emitDef emitted extension allocated bounded
    (by intro live operand member; exact children.2 live operand (by simpa [Op.uses] using member))
    (by intro _ address impossible; cases impossible) (by intro _ fn args origin impossible; cases impossible)
  exact ⟨children.1.trans tail, result⟩

theorem SourceReadyFrame.structure (frame : SourceReadyFrame module callees func types state completed)
    {elementType : Ty} {expressions : List Expr} {inputs : List ValueId}
    (childrenRun : lowerExprs expressions env before = (inputs, middle))
    (run : lowerExpr (.structLit elementType expressions) env before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound middle)
    (children : EmitsOnly (ReadyOperands state) before middle ∧
      (middle.cur.isSome = true → ∀ input ∈ inputs, flowAt state.values input ≠ .pending)) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  have emitted : Lower.emitDef (.structLit elementType inputs) env middle = (value, after) := by
    simpa only [lowerExpr, bind_run, childrenRun] using run
  obtain ⟨tail, result⟩ := frame.emitDef emitted extension allocated bounded
    (by intro live operand member; exact children.2 live operand (by simpa [Op.uses] using member))
    (by intro _ address impossible; cases impossible) (by intro _ fn args origin impossible; cases impossible)
  exact ⟨children.1.trans tail, result⟩

#print axioms SourceReadyFrame.length
#print axioms SourceReadyFrame.fill
#print axioms SourceReadyFrame.pop
#print axioms SourceReadyFrame.array
#print axioms SourceReadyFrame.structure

end Goose.Lower.Validation.ReplacementContentFlowSource
