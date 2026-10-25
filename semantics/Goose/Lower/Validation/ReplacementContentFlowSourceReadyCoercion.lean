import Goose.Lower.Validation.ReplacementContentFlowSourceReadyEmit

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.coerceTo {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before after : LS}
    {env : LEnv} {input output : ValueId} {target : Ty} {origin : OriginId}
    (frame : SourceReadyFrame module callees func types state completed)
    (run : Lower.coerceTo target input origin env before = (output, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound before)
    (available : before.cur.isSome = true → flowAt state.values input ≠ .pending) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values output ≠ .pending) := by
  unfold Lower.coerceTo at run
  obtain ⟨type, classified, classifyRun, tailRun⟩ := bind_eq.mp run
  have same : classified = before := valTy_eq classifyRun
  subst classified
  split at tailRun
  · exact frame.emitDef tailRun extension allocated bounded
      (by intro live operand member; have same : operand = input := by simpa [Op.uses] using member
          subst operand; exact available live)
      (by intro _ address impossible; cases impossible) (by intro _ fn args org impossible; cases impossible)
  · obtain ⟨view, middle, viewRun, sliceRun⟩ := bind_eq.mp tailRun
    have rest := adv_emitDef sliceRun
    have first := adv_emitDef viewRun
    obtain ⟨viewEmits, viewReady⟩ := frame.emitDef viewRun (rest.ext.trans extension)
      (Nat.le_trans rest.vals allocated) bounded
      (by intro live operand member; have same : operand = input := by simpa [Op.uses] using member
          subst operand; exact available live)
      (by intro _ address impossible; cases impossible) (by intro _ fn args org impossible; cases impossible)
    obtain ⟨sliceEmits, sliceReady⟩ := frame.emitDef sliceRun extension allocated
      (liveBound_of_adv first bounded)
      (by intro live operand member; have same : operand = view := by simpa [Op.uses, Bnd.uses] using member
          subst operand; exact viewReady live)
      (by intro _ address impossible; cases impossible) (by intro _ fn args org impossible; cases impossible)
    exact ⟨viewEmits.trans sliceEmits, sliceReady⟩
  · obtain ⟨rfl, rfl⟩ := pure_eq.mp tailRun
    exact ⟨.refl _ _, available⟩

theorem SourceReadyFrame.coerceSlot {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before after : LS}
    {env : LEnv} {input output : ValueId} {slot : SlotId} {origin : OriginId}
    (frame : SourceReadyFrame module callees func types state completed)
    (run : Lower.coerceSlot slot input origin env before = (output, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound before)
    (available : before.cur.isSome = true → flowAt state.values input ≠ .pending) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values output ≠ .pending) := by
  change (match env.slots[slot]? with
    | some destination => Lower.coerceTo destination.ty input origin
    | none => pure input) env before = (output, after) at run
  cases selected : env.slots[slot]? with
  | some destination =>
    rw [selected] at run
    exact frame.coerceTo run extension allocated bounded available
  | none =>
    rw [selected] at run
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    exact ⟨.refl _ _, available⟩

theorem SourceReadyFrame.coerceResult {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before after : LS}
    {env : LEnv} {input output : ValueId} {origin : OriginId}
    (frame : SourceReadyFrame module callees func types state completed)
    (run : Lower.coerceResult input origin env before = (output, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound before)
    (available : before.cur.isSome = true → flowAt state.values input ≠ .pending) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values output ≠ .pending) := by
  change (match env.results.head? with
    | some destination => Lower.coerceTo destination input origin
    | none => pure input) env before = (output, after) at run
  cases selected : env.results.head? with
  | some destination =>
    rw [selected] at run
    exact frame.coerceTo run extension allocated bounded available
  | none =>
    rw [selected] at run
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    exact ⟨.refl _ _, available⟩

#print axioms SourceReadyFrame.coerceTo
#print axioms SourceReadyFrame.coerceSlot
#print axioms SourceReadyFrame.coerceResult

end Goose.Lower.Validation.ReplacementContentFlowSource
