import Goose.Lower.DemandRuntimePrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem DemandInstructionStep.runtime {cx : FnCtx} {fuel : Nat} {before after : DemandRuntimePoint}
    (step : DemandInstructionStep cx fuel before after) :
    Evidence.RuntimeStep cx.cfg cx.fn before.point before.frame before.state after.point after.frame after.state := by
  cases step with
  | definition instruction execution => exact .define instruction execution
  | effect instruction execution => exact .effect instruction execution
  | @control point frame next state after branch target instruction execution =>
    cases branch with
    | jump destination arguments =>
      simp only [DemandBranch.enter, bind_apply] at execution
      cases read : mapList (getCell frame) arguments state with
      | stop reason stopped => simp [read] at execution
      | ok values readState =>
        simp only [read] at execution
        cases entered : enterBlock cx.fn frame destination values readState with
        | stop reason stopped => simp [entered] at execution
        | ok pair final =>
          cases pair with
          | mk code nextFrame =>
            simp only [entered, pure_apply, Res.ok.injEq, Prod.mk.injEq] at execution
            obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := execution
            exact .branch instruction read entered
    | conditional condition yes yesArguments no noArguments =>
      simp only [DemandBranch.enter, bind_apply] at execution
      cases readCondition : getVal frame condition state with
      | stop reason stopped => simp [readCondition] at execution
      | ok value testedState =>
        simp only [readCondition] at execution
        cases tested : expectBool value testedState with
        | stop reason stopped => simp [tested] at execution
        | ok boolean readState =>
          simp only [tested] at execution
          have conditionRun : (getVal frame condition >>= expectBool) state = .ok boolean readState := by
            simp only [bind_apply, readCondition, tested]
          cases boolean with
          | false =>
            simp only [Bool.false_eq_true, ite_false, bind_apply] at execution
            cases read : mapList (getCell frame) noArguments readState with
            | stop reason stopped => simp [read] at execution
            | ok values afterRead =>
              simp only [read] at execution
              cases entered : enterBlock cx.fn frame no values afterRead with
              | stop reason stopped => simp [entered] at execution
              | ok pair final =>
                cases pair with
                | mk code nextFrame =>
                  simp only [entered, pure_apply, Res.ok.injEq, Prod.mk.injEq] at execution
                  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := execution
                  exact .branchFalse instruction conditionRun read entered
          | true =>
            simp only [ite_true, bind_apply] at execution
            cases read : mapList (getCell frame) yesArguments readState with
            | stop reason stopped => simp [read] at execution
            | ok values afterRead =>
              simp only [read] at execution
              cases entered : enterBlock cx.fn frame yes values afterRead with
              | stop reason stopped => simp [entered] at execution
              | ok pair final =>
                cases pair with
                | mk code nextFrame =>
                  simp only [entered, pure_apply, Res.ok.injEq, Prod.mk.injEq] at execution
                  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := execution
                  exact .branchTrue instruction conditionRun read entered

theorem DemandPrefix.runtime {cx : FnCtx} {taken fuel : Nat} {before after : DemandRuntimePoint}
    (steps : DemandPrefix cx taken fuel before after) : DemandRuntimePrefix cx taken before after := by
  induction steps with
  | zero => exact .zero _
  | next step rest ih => exact .next step.runtime ih

theorem runAt_maximal_demand_prefix {cx : FnCtx} (fuel : Nat) (initial : DemandRuntimePoint) :
    ∃ taken remaining terminal,
      taken + remaining = fuel ∧ DemandPrefix cx taken fuel initial terminal ∧
      GIR.runAt cx initial.point initial.frame fuel initial.state =
        GIR.runAt cx terminal.point terminal.frame remaining terminal.state ∧
      (remaining = 0 ∨ ∀ next, ¬ DemandInstructionStep cx (remaining - 1) terminal next) := by
  induction fuel generalizing initial with
  | zero => exact ⟨0, 0, initial, rfl, .zero _ _, rfl, Or.inl rfl⟩
  | succ fuel ih =>
    classical
    by_cases possible : ∃ next, DemandInstructionStep cx fuel initial next
    · obtain ⟨next, step⟩ := possible
      obtain ⟨taken, remaining, terminal, count, traversed, run, maximal⟩ := ih next
      exact ⟨taken + 1, remaining, terminal, by omega, .next step traversed, step.runAt.trans run, maximal⟩
    · exact ⟨0, fuel + 1, initial, by omega, .zero _ _, rfl, Or.inr (by simpa using possible)⟩

theorem runAt_nonTimeout_stopped_prefix {cx : FnCtx} {fuel : Nat} {initial : DemandRuntimePoint}
    {stop : Stop} {after : St} (nonTimeout : stop ≠ .timeout)
    (run : GIR.runAt cx initial.point initial.frame fuel initial.state = .stop stop after) :
    ∃ taken remaining terminal,
      taken + remaining = fuel ∧ DemandRuntimePrefix cx taken initial terminal ∧
      GIR.runAt cx terminal.point terminal.frame remaining terminal.state = .stop stop after ∧
      (∀ next, ¬ DemandInstructionStep cx (remaining - 1) terminal next) ∧
      (DemandInstructionStop cx remaining terminal stop after ∨
        (∃ term, instAt cx.fn terminal.point = some (.term term)) ∨ instAt cx.fn terminal.point = none) := by
  obtain ⟨taken, remaining, terminal, count, traversed, same, maximal⟩ := runAt_maximal_demand_prefix fuel initial
  have terminalRun : GIR.runAt cx terminal.point terminal.frame remaining terminal.state = .stop stop after := same.symm.trans run
  cases remaining with
  | zero =>
    change timeout terminal.state = .stop stop after at terminalRun
    simp [timeout, M.stop] at terminalRun
    exact (nonTimeout terminalRun.1.symm).elim
  | succ remaining =>
    have noStep : ∀ next, ¬ DemandInstructionStep cx remaining terminal next := by
      rcases maximal with zero | maximal
      · omega
      · simpa using maximal
    refine ⟨taken, remaining + 1, terminal, count, traversed.runtime, terminalRun, ?_, ?_⟩
    · simpa using noStep
    cases instruction : instAt cx.fn terminal.point with
    | none => exact Or.inr (Or.inr rfl)
    | some inst =>
      cases inst with
      | term term => exact Or.inr (Or.inl ⟨term, rfl⟩)
      | «def» id op =>
        cases evaluated : execOp remaining cx terminal.frame op terminal.state with
        | ok value state => exact (noStep _ (.definition instruction evaluated)).elim
        | stop reason state =>
          have halted : DemandInstructionStop cx (remaining + 1) terminal reason state := .definition instruction evaluated
          have equal := halted.runAt.symm.trans terminalRun
          obtain ⟨rfl, rfl⟩ := Res.stop.inj equal
          exact Or.inl halted
      | eff effect =>
        cases evaluated : execEff cx.fn terminal.frame effect terminal.state with
        | ok frame state => exact (noStep _ (.effect instruction evaluated)).elim
        | stop reason state =>
          have halted : DemandInstructionStop cx (remaining + 1) terminal reason state := .effect instruction evaluated
          have equal := halted.runAt.symm.trans terminalRun
          obtain ⟨rfl, rfl⟩ := Res.stop.inj equal
          exact Or.inl halted

#print axioms DemandInstructionStep.runtime
#print axioms DemandPrefix.runtime
#print axioms runAt_maximal_demand_prefix
#print axioms runAt_nonTimeout_stopped_prefix
end Goose.Lower
