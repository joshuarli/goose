import Goose.Lower.DemandTrace
import Goose.Evidence.Execution
import Goose.Proofs.GIRFuel

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Evidence Goose.Core.Sound

theorem DemandInstructionStep.mono_fuel {cx : FnCtx} {fuel larger : Nat}
    {before after : DemandRuntimePoint} (step : DemandInstructionStep cx fuel before after)
    (bound : fuel ≤ larger) : DemandInstructionStep cx larger before after := by
  cases step with
  | definition instruction execution =>
    exact .definition instruction (Goose.Proofs.GIRFuel.execOp_success_fuel_mono bound execution)
  | effect instruction execution => exact .effect instruction execution
  | control instruction execution => exact .control instruction execution

theorem DemandInstructionStep.deterministic_across_fuel {cx : FnCtx} {firstFuel secondFuel : Nat}
    {before firstAfter secondAfter : DemandRuntimePoint}
    (first : DemandInstructionStep cx firstFuel before firstAfter)
    (second : DemandInstructionStep cx secondFuel before secondAfter) : firstAfter = secondAfter :=
  (first.mono_fuel (Nat.le_max_left firstFuel secondFuel)).deterministic
    (second.mono_fuel (Nat.le_max_right firstFuel secondFuel))

theorem DemandInstructionStop.excludes_step_nonTimeout {cx : FnCtx} {stoppedFuel stepFuel : Nat}
    {before after : DemandRuntimePoint} {stop : Stop} {finalState : St}
    (stopped : DemandInstructionStop cx stoppedFuel before stop finalState) (nonTimeout : stop ≠ .timeout)
    (step : DemandInstructionStep cx stepFuel before after) : False := by
  cases stopped with
  | timeout => exact nonTimeout rfl
  | @definition fuel point id op stop after instruction execution =>
    cases step with
    | definition instruction' execution' =>
      have same := instruction.symm.trans instruction'
      cases same
      have stops := Goose.Proofs.GIRFuel.execOp_stop_fuel_mono (k := fuel + stepFuel)
        (by omega) nonTimeout execution
      have succeeds := Goose.Proofs.GIRFuel.execOp_success_fuel_mono (k := fuel + stepFuel)
        (by omega) execution'
      cases stops.symm.trans succeeds
    | effect instruction' execution' => cases instruction.symm.trans instruction'
    | control instruction' execution' => cases instruction.symm.trans instruction'
  | effect instruction execution =>
    cases step with
    | definition instruction' execution' => cases instruction.symm.trans instruction'
    | effect instruction' execution' =>
      have same := instruction.symm.trans instruction'
      cases same
      cases execution.symm.trans execution'
    | control instruction' execution' => cases instruction.symm.trans instruction'

theorem runtimeStep_demandInstructionStep {cx : FnCtx} {point next : Pt}
    {frame final : GIR.Frame} {state after : St}
    (step : RuntimeStep cx.cfg cx.fn point frame state next final after) :
    ∃ fuel, DemandInstructionStep cx fuel ⟨point, frame, state⟩ ⟨next, final, after⟩ := by
  cases step with
  | define instruction execution => exact ⟨_, .definition instruction execution⟩
  | effect instruction execution => exact ⟨0, .effect instruction execution⟩
  | branch instruction read enter =>
    refine ⟨0, .control (branch := .jump _ _) instruction ?_⟩
    simp only [DemandBranch.enter, bind_apply, read, enter, pure_apply]
  | @branchTrue condition target arguments other otherArguments tested values readState final after instruction test read enter =>
    refine ⟨0, .control (branch := .conditional _ _ _ _ _) instruction ?_⟩
    cases found : getVal frame condition state with
    | stop stop after => simp only [bind_apply, found] at test; cases test
    | ok value intermediate =>
      simp only [bind_apply, found] at test
      simp only [DemandBranch.enter, bind_apply, found, test, ite_true, read, enter, pure_apply]
  | @branchFalse condition other otherArguments target arguments tested values readState final after instruction test read enter =>
    refine ⟨0, .control (branch := .conditional _ _ _ _ _) instruction ?_⟩
    cases found : getVal frame condition state with
    | stop stop after => simp only [bind_apply, found] at test; cases test
    | ok value intermediate =>
      simp only [bind_apply, found] at test
      simp only [DemandBranch.enter, bind_apply, found, test, Bool.false_eq_true, ite_false,
        read, enter, pure_apply]

inductive DemandRuntimePrefix (cx : FnCtx) : Nat → DemandRuntimePoint → DemandRuntimePoint → Prop
  | zero (point : DemandRuntimePoint) : DemandRuntimePrefix cx 0 point point
  | next {length : Nat} {before middle after : DemandRuntimePoint}
      (step : RuntimeStep cx.cfg cx.fn before.point before.frame before.state middle.point middle.frame middle.state)
      (rest : DemandRuntimePrefix cx length middle after) :
      DemandRuntimePrefix cx (length + 1) before after

theorem DemandRuntimePrefix.uncons {cx : FnCtx} {length : Nat} {before after : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx length before after) :
    (length = 0 ∧ after = before) ∨
      ∃ rest middle, length = rest + 1 ∧
        RuntimeStep cx.cfg cx.fn before.point before.frame before.state middle.point middle.frame middle.state ∧
        DemandRuntimePrefix cx rest middle after := by
  cases steps with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | next step rest => exact Or.inr ⟨_, _, rfl, step, rest⟩

theorem DemandRuntimePrefix.append {cx : FnCtx} {firstLength restLength : Nat}
    {before middle after : DemandRuntimePoint}
    (first : DemandRuntimePrefix cx firstLength before middle)
    (rest : DemandRuntimePrefix cx restLength middle after) :
    DemandRuntimePrefix cx (firstLength + restLength) before after := by
  induction first with
  | zero => simpa only [Nat.zero_add] using rest
  | next step steps induction =>
    have combined := DemandRuntimePrefix.next step (induction rest)
    simpa only [Nat.add_right_comm] using combined

theorem DemandRuntimePrefix.reachable {cx : FnCtx} {length : Nat} {before after : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx length before after)
    (reached : RuntimePoint cx.cfg cx.fn before.point before.frame before.state) :
    RuntimePoint cx.cfg cx.fn after.point after.frame after.state := by
  induction steps with
  | zero => exact reached
  | next step rest induction => exact induction (RuntimePoint.step reached step)

theorem DemandUniformTraversal.runtimePrefix_invariant {cx : FnCtx} {invariant : DemandRuntimePoint → Prop}
    {length : Nat} {before after : DemandRuntimePoint}
    (traversal : DemandUniformTraversal cx invariant length before after)
    {taken : Nat} {reached : DemandRuntimePoint}
    (bounded : taken ≤ length) (steps : DemandRuntimePrefix cx taken before reached) : invariant reached := by
  induction traversal generalizing taken reached with
  | done valid =>
    have zero : taken = 0 := by omega
    subst taken
    cases steps
    exact valid
  | next valid step rest induction =>
    cases steps with
    | zero => exact valid
    | next first tail =>
      obtain ⟨fuel, first⟩ := runtimeStep_demandInstructionStep first
      have same := (step fuel).deterministic first
      cases same
      exact induction (by omega) tail

theorem DemandTraversal.runtimePrefix_invariant {cx : FnCtx} {invariant : DemandRuntimePoint → Prop}
    {length fuel : Nat} {before after : DemandRuntimePoint}
    (traversal : DemandTraversal cx invariant length fuel before after)
    {taken : Nat} {reached : DemandRuntimePoint}
    (bounded : taken ≤ length) (steps : DemandRuntimePrefix cx taken before reached) : invariant reached := by
  induction traversal generalizing taken reached with
  | done fuel valid =>
    have zero : taken = 0 := by omega
    subst taken
    cases steps
    exact valid
  | next valid step rest induction =>
    cases steps with
    | zero => exact valid
    | next first tail =>
      obtain ⟨_, first⟩ := runtimeStep_demandInstructionStep first
      have same := step.deterministic_across_fuel first
      cases same
      exact induction (by omega) tail

theorem DemandStoppedTraversal.runtimePrefix_invariant {cx : FnCtx} {invariant : DemandRuntimePoint → Prop}
    {length fuel : Nat} {before : DemandRuntimePoint} {stop : Stop} {after : St}
    (traversal : DemandStoppedTraversal cx invariant length fuel before stop after)
    (nonTimeout : stop ≠ .timeout) {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken before reached) : invariant reached := by
  obtain ⟨checkpoint, traversal, stopped⟩ := traversal
  induction traversal generalizing taken reached with
  | done fuel valid =>
    cases steps with
    | zero => exact valid
    | next first rest =>
      obtain ⟨_, first⟩ := runtimeStep_demandInstructionStep first
      exact (stopped.excludes_step_nonTimeout nonTimeout first).elim
  | next valid step rest induction =>
    cases steps with
    | zero => exact valid
    | next first tail =>
      obtain ⟨_, first⟩ := runtimeStep_demandInstructionStep first
      have same := step.deterministic_across_fuel first
      cases same
      exact induction tail (by simpa only [Nat.add_sub_add_right] using stopped)

end Goose.Lower
