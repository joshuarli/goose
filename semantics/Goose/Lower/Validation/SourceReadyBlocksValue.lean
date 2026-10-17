import Goose.Lower.Validation.SourceReadyBlocks

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.lowerBlockValue {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS} {env : LEnv}
    {want : Bool} {value : Option Expr}
    (frame : SourceReadyFrame module callees func types state completed)
    (extension : (Goose.Lower.lowerBlockValue want value env before).2.Ext completed)
    (allocated : (Goose.Lower.lowerBlockValue want value env before).2.vals.size ≤ completed.vals.size)
    (bounded : LiveBound before)
    (child : ∀ expression, value = some expression → ValueReadyAt state (lowerExpr expression) env before) :
    EmitsOnly (ReadyOperands state) before (Goose.Lower.lowerBlockValue want value env before).2 ∧
      (want = true → (Goose.Lower.lowerBlockValue want value env before).2.cur.isSome = true →
        flowAt state.values (Goose.Lower.lowerBlockValue want value env before).1 ≠ .pending) := by
  cases value with
  | some expression => exact ⟨(child expression rfl).1, fun _ => (child expression rfl).2⟩
  | none =>
    cases want with
    | false => exact ⟨.refl _ _, by simp⟩
    | true =>
      have unitReady := frame.emitDef (show Goose.Lower.emitDef .constUnit env before =
        Goose.Lower.emitDef .constUnit env before from rfl) extension allocated bounded
        (by intro _ operand member; simp [Op.uses] at member)
        (by intro _ address impossible; cases impossible) (by intro _ fn args origin impossible; cases impossible)
      exact ⟨unitReady.1, fun _ => unitReady.2⟩

#print axioms SourceReadyFrame.lowerBlockValue

end Goose.Lower.Validation.ReplacementContentFlowSource
