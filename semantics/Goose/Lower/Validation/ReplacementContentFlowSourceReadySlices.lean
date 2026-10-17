import Goose.Lower.Validation.ReplacementContentFlowSourceReadyEmit
import Goose.Lower.Validation.DeadFrontier

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

def BoundaryReadyAt (state : State) (bound : Bound) (env : LEnv) (before : LS) : Prop :=
  EmitsOnly (ReadyOperands state) before (lowerBound bound env before).2 ∧
    ((lowerBound bound env before).2.cur.isSome = true →
      ∀ value ∈ (lowerBound bound env before).1.uses, flowAt state.values value ≠ .pending)

theorem lowerBound_ready {state : State} {bound : Bound} {env : LEnv} {before : LS}
    (child : ∀ expression, bound = .expr expression ∨ bound = .fromEnd expression →
      ValueReadyAt state (lowerExpr expression) env before) :
    BoundaryReadyAt state bound env before := by
  cases bound with
  | omitted => exact ⟨.refl _ _, by simp [lowerBound, pure_run, Bnd.uses]⟩
  | expr expression =>
    obtain ⟨emitted, available⟩ := child expression (Or.inl rfl)
    refine ⟨?_, ?_⟩
    · simpa only [lowerBound, bind_run, pure_run] using emitted
    · intro live value member
      have same : value = (lowerExpr expression env before).1 := by
        simpa only [lowerBound, bind_run, pure_run, Bnd.uses, List.mem_singleton] using member
      subst value
      exact available live
  | fromEnd expression =>
    obtain ⟨emitted, available⟩ := child expression (Or.inr rfl)
    refine ⟨?_, ?_⟩
    · simpa only [lowerBound, bind_run, pure_run] using emitted
    · intro live value member
      have same : value = (lowerExpr expression env before).1 := by
        simpa only [lowerBound, bind_run, pure_run, Bnd.uses, List.mem_singleton] using member
      subst value
      exact available live

theorem SourceReadyFrame.slice {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before first second middle after : LS}
    {env : LEnv} {view : View} {low high : Bound} {origin : OriginId} {mutability : Mutability}
    {viewValue value : ValueId} {lowValue highValue : Bnd}
    (frame : SourceReadyFrame module callees func types state completed)
    (viewRun : lowerView view env before = (viewValue, first))
    (lowRun : lowerBound low env first = (lowValue, second))
    (highRun : lowerBound high env second = (highValue, middle))
    (run : lowerExpr (.slice mutability view low high origin) env before = (value, after))
    (extension : after.Ext completed) (allocated : after.vals.size ≤ completed.vals.size)
    (bounded : LiveBound middle)
    (viewReady : EmitsOnly (ReadyOperands state) before first ∧
      (first.cur.isSome = true → flowAt state.values viewValue ≠ .pending))
    (lowReady : BoundaryReadyAt state low env first)
    (highReady : BoundaryReadyAt state high env second) :
    EmitsOnly (ReadyOperands state) before after ∧
      (after.cur.isSome = true → flowAt state.values value ≠ .pending) := by
  rw [BoundaryReadyAt, lowRun] at lowReady
  rw [BoundaryReadyAt, highRun] at highReady
  have emitted : Lower.emitDef (.viewSlice mutability viewValue lowValue highValue (some origin)) env middle = (value, after) := by
    simpa only [lowerExpr, bind_run, viewRun, lowRun, highRun] using run
  obtain ⟨tail, available⟩ := frame.emitDef emitted extension allocated bounded
    (by
      intro live operand member
      have secondLive := (dead_lowerBound high).live_before highRun live
      have firstLive := (dead_lowerBound low).live_before lowRun secondLive
      rcases (show operand = viewValue ∨ operand ∈ lowValue.uses ∨ operand ∈ highValue.uses from by
        simpa [Op.uses] using member) with same | lowMember | highMember
      · subst operand; exact viewReady.2 firstLive
      · exact lowReady.2 secondLive operand lowMember
      · exact highReady.2 live operand highMember)
    (by intro _ address impossible; cases impossible) (by intro _ fn args org impossible; cases impossible)
  exact ⟨viewReady.1.trans (lowReady.1.trans (highReady.1.trans tail)), available⟩

#print axioms lowerBound_ready
#print axioms SourceReadyFrame.slice

end Goose.Lower.Validation.ReplacementContentFlowSource
