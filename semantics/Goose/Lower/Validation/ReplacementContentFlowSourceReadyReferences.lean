import Goose.Lower.Validation.ReplacementContentFlowSourceReadyEmit

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {callees : Array State} {func : Func}
  {types : Array (Option VTy)} {state : State} {completed before after : LS}
  {env : LEnv} {input output : ValueId} {mutability : Mutability}

theorem SourceReadyFrame.freezeTo (frame : SourceReadyFrame module callees func types state completed)
    (run : Lower.freezeTo mutability input env before = (output, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound before)
    (available : before.cur.isSome = true → flowAt state.values input ≠ .pending) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values output ≠ .pending) := by
  unfold Lower.freezeTo at run
  obtain ⟨type, classified, classifyRun, tailRun⟩ := bind_eq.mp run
  have same : classified = before := valTy_eq classifyRun
  subst classified
  split at tailRun
  · exact frame.emitDef tailRun extension allocated bounded
      (by intro live operand member; have same : operand = input := by simpa [Op.uses] using member
          subst operand; exact available live)
      (by intro _ address impossible; cases impossible) (by intro _ fn args org impossible; cases impossible)
  · obtain ⟨rfl, rfl⟩ := pure_eq.mp tailRun
    exact ⟨.refl _ _, available⟩

theorem SourceReadyFrame.borrowTo (frame : SourceReadyFrame module callees func types state completed)
    (run : Lower.borrowTo mutability input env before = (output, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound before)
    (available : before.cur.isSome = true → flowAt state.values input ≠ .pending) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values output ≠ .pending) := by
  have classification : valTy input env before = ((valTy input env before).1, before) :=
    Prod.ext rfl (valTy_eq rfl)
  change (if mutability == .mutable && env.mod.profile == .shrink &&
      (match (valTy input env before).1 with
       | .data (.ref .mutable (.grow _)) | .data (.ref .mutable (.growshrink _)) |
         .data (.ref .mutable (.limited _ _)) => true
       | _ => false) then Lower.emitDef (.ownerBorrow input) else Lower.freezeTo mutability input)
      env (valTy input env before).2 = (output, after) at run
  rw [classification] at run
  by_cases borrowed : (mutability == .mutable && env.mod.profile == .shrink &&
      (match (valTy input env before).1 with
       | .data (.ref .mutable (.grow _)) | .data (.ref .mutable (.growshrink _)) |
         .data (.ref .mutable (.limited _ _)) => true
       | _ => false)) = true
  · rw [if_pos borrowed] at run
    exact frame.emitDef run extension allocated bounded
      (by intro live operand member; have same : operand = input := by simpa [Op.uses] using member
          subst operand; exact available live)
      (by intro _ address impossible; cases impossible) (by intro _ fn args org impossible; cases impossible)
  · rw [if_neg borrowed] at run
    exact frame.freezeTo run extension allocated bounded available

theorem SourceReadyFrame.reference (frame : SourceReadyFrame module callees func types state completed)
    {place : Place} {middle : LS}
    (childRun : lowerPlace place env before = (input, middle))
    (run : lowerExpr (.ref mutability place) env before = (output, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound middle)
    (child : EmitsOnly (ReadyOperands state) before middle ∧
      (middle.cur.isSome = true → flowAt state.values input ≠ .pending)) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values output ≠ .pending) := by
  have emitted : Lower.borrowTo mutability input env middle = (output, after) := by
    simpa only [lowerExpr, bind_run, childRun] using run
  obtain ⟨tail, result⟩ := frame.borrowTo emitted extension allocated bounded child.2
  exact ⟨child.1.trans tail, result⟩

theorem SourceReadyFrame.argumentReference (frame : SourceReadyFrame module callees func types state completed)
    {place : Place} {middle : LS}
    (childRun : lowerPlace place env before = (input, middle))
    (run : lowerArg (.byRef mutability place) env before = (output, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound middle)
    (child : EmitsOnly (ReadyOperands state) before middle ∧
      (middle.cur.isSome = true → flowAt state.values input ≠ .pending)) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values output ≠ .pending) := by
  have emitted : Lower.borrowTo mutability input env middle = (output, after) := by
    simpa only [lowerArg, bind_run, childRun] using run
  obtain ⟨tail, result⟩ := frame.borrowTo emitted extension allocated bounded child.2
  exact ⟨child.1.trans tail, result⟩

#print axioms SourceReadyFrame.reference
#print axioms SourceReadyFrame.argumentReference

#print axioms SourceReadyFrame.freezeTo
#print axioms SourceReadyFrame.borrowTo

end Goose.Lower.Validation.ReplacementContentFlowSource
