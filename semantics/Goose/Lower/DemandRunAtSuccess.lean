import Goose.Lower.DemandRunAtPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem runAt_success_maximal_prefix {cx : FnCtx} {fuel : Nat} {initial : DemandRuntimePoint}
    {value : Val} {after : St} (run : GIR.runAt cx initial.point initial.frame fuel initial.state = .ok value after) :
    ∃ taken remaining terminal,
      taken + remaining = fuel ∧ DemandRuntimePrefix cx taken initial terminal ∧
      GIR.runAt cx terminal.point terminal.frame remaining terminal.state = .ok value after ∧
      (∀ next, ¬ DemandInstructionStep cx (remaining - 1) terminal next) ∧
      (∀ instruction, instAt cx.fn terminal.point = some instruction → ∃ term, instruction = .term term) := by
  obtain ⟨taken, remaining, terminal, count, traversed, same, maximal⟩ := runAt_maximal_demand_prefix fuel initial
  have terminalRun := same.symm.trans run
  cases remaining with
  | zero =>
    change timeout terminal.state = .ok value after at terminalRun
    simp [timeout, M.stop] at terminalRun
  | succ remaining =>
    have noStep : ∀ next, ¬ DemandInstructionStep cx remaining terminal next := by
      rcases maximal with zero | maximal
      · omega
      · simpa using maximal
    refine ⟨taken, remaining + 1, terminal, count, traversed.runtime, terminalRun, ?_, ?_⟩
    · simpa using noStep
    · intro instruction atPoint
      cases instruction with
      | term term => exact ⟨term, rfl⟩
      | «def» id op =>
        cases evaluated : execOp remaining cx terminal.frame op terminal.state with
        | ok result state => exact (noStep _ (.definition atPoint evaluated)).elim
        | stop reason state =>
          have halted : DemandInstructionStop cx (remaining + 1) terminal reason state := .definition atPoint evaluated
          have equal := halted.runAt.symm.trans terminalRun
          cases equal
      | eff effect =>
        cases evaluated : execEff cx.fn terminal.frame effect terminal.state with
        | ok frame state => exact (noStep _ (.effect atPoint evaluated)).elim
        | stop reason state =>
          have halted : DemandInstructionStop cx (remaining + 1) terminal reason state := .effect atPoint evaluated
          have equal := halted.runAt.symm.trans terminalRun
          cases equal

#print axioms runAt_success_maximal_prefix
end Goose.Lower
