import Goose.Lower.Validation.ReplacementContentFlowSourceReadyEmit
import Goose.Lower.Validation.DeadFrontier

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.push {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before first middle after : LS}
    {env : LEnv} {owner : Place} {expression : Expr} {origin : OriginId}
    {address input value : ValueId}
    (frame : SourceReadyFrame module callees func types state completed)
    (ownerRun : lowerPlace owner env before = (address, first))
    (valueRun : lowerExpr expression env first = (input, middle))
    (run : lowerExpr (.push owner expression origin) env before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound middle)
    (ownerReady : EmitsOnly (ReadyOperands state) before first ∧
      (first.cur.isSome = true → flowAt state.values address ≠ .pending))
    (valueReady : EmitsOnly (ReadyOperands state) first middle ∧
      (middle.cur.isSome = true → flowAt state.values input ≠ .pending)) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  have emitted : Lower.emitDef (.push address input origin) env middle = (value, after) := by
    simpa only [lowerExpr, bind_run, ownerRun, valueRun] using run
  obtain ⟨tail, ready⟩ := frame.emitDef emitted extension allocated bounded
    (by
      intro live operand member
      rcases (show operand = address ∨ operand = input from by simpa [Op.uses] using member) with same | same
      · subst operand; exact ownerReady.2 ((dead_lowerExpr expression).live_before valueRun live)
      · subst operand; exact valueReady.2 live)
    (by intro _ address impossible; cases impossible) (by intro _ fn args org impossible; cases impossible)
  exact ⟨ownerReady.1.trans (valueReady.1.trans tail), ready⟩

#print axioms SourceReadyFrame.push

end Goose.Lower.Validation.ReplacementContentFlowSource
