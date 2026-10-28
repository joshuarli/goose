import Goose.Lower.DemandRuntimePrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Evidence Goose.Core.Sound

theorem DemandRuntimePrefix.split_at {cx : FnCtx} {length : Nat} {before middle : DemandRuntimePoint}
    (known : DemandRuntimePrefix cx length before middle)
    {taken : Nat} {reached : DemandRuntimePoint}
    (bounded : length ≤ taken) (steps : DemandRuntimePrefix cx taken before reached) :
    ∃ remaining, taken = length + remaining ∧ DemandRuntimePrefix cx remaining middle reached := by
  induction known generalizing taken reached with
  | zero => exact ⟨taken, by omega, steps⟩
  | @next count begin intermediate finish first tail ih =>
    cases steps with
    | zero => omega
    | @next restCount begin actualMiddle finish actual rest =>
      obtain ⟨firstFuel, firstStep⟩ := runtimeStep_demandInstructionStep first
      obtain ⟨actualFuel, actualStep⟩ := runtimeStep_demandInstructionStep actual
      have same := firstStep.deterministic_across_fuel actualStep
      have points : intermediate = actualMiddle := by
        cases intermediate
        cases actualMiddle
        exact same
      subst actualMiddle
      obtain ⟨remaining, count, residual⟩ := ih (by omega) rest
      exact ⟨remaining, by omega, residual⟩

#print axioms DemandRuntimePrefix.split_at
end Goose.Lower
