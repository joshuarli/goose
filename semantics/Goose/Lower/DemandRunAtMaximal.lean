import Goose.Lower.DemandRunAtPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR

theorem runAt_nonTimeout_maximal_prefix {cx : FnCtx} {fuel : Nat} {initial : DemandRuntimePoint}
    {stop : Stop} {after : St} (nonTimeout : stop ≠ .timeout)
    (run : GIR.runAt cx initial.point initial.frame fuel initial.state = .stop stop after) :
    ∃ taken remaining terminal,
      taken + remaining = fuel ∧ 0 < remaining ∧ DemandRuntimePrefix cx taken initial terminal ∧
      GIR.runAt cx terminal.point terminal.frame remaining terminal.state = .stop stop after ∧
      ∀ next, ¬ DemandInstructionStep cx (remaining - 1) terminal next := by
  obtain ⟨taken, remaining, terminal, count, traversal, same, maximal⟩ := runAt_maximal_demand_prefix fuel initial
  have terminalRun := same.symm.trans run
  rcases maximal with zero | maximal
  · subst remaining
    change timeout terminal.state = .stop stop after at terminalRun
    simp [timeout, M.stop] at terminalRun
    exact (nonTimeout terminalRun.1.symm).elim
  · have positive : 0 < remaining := by
      cases remaining with
      | zero =>
        change timeout terminal.state = .stop stop after at terminalRun
        simp [timeout, M.stop] at terminalRun
        exact (nonTimeout terminalRun.1.symm).elim
      | succ remaining => omega
    exact ⟨taken, remaining, terminal, count, positive, traversal.runtime, terminalRun, maximal⟩

#print axioms runAt_nonTimeout_maximal_prefix
end Goose.Lower
