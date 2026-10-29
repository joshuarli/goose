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

theorem DemandRuntimePrefix.split_length {cx : FnCtx} {length taken : Nat} {before reached : DemandRuntimePoint}
    (bounded : length ≤ taken) (steps : DemandRuntimePrefix cx taken before reached) :
    ∃ middle, DemandRuntimePrefix cx length before middle ∧
      DemandRuntimePrefix cx (taken - length) middle reached := by
  induction length generalizing taken before with
  | zero => exact ⟨before, .zero _, by simpa using steps⟩
  | succ length ih =>
    cases steps with
    | zero => omega
    | @next rest begin middle finish first tail =>
      obtain ⟨boundary, leading, suffix⟩ := ih (by omega) tail
      refine ⟨boundary, ?_, ?_⟩
      · simpa [Nat.add_comm] using DemandRuntimePrefix.next first leading
      · simpa using suffix

theorem DemandRuntimePrefix.length_le_stopped {cx : FnCtx} {length taken : Nat}
    {before finish reached : DemandRuntimePoint} (known : DemandRuntimePrefix cx length before finish)
    (steps : DemandRuntimePrefix cx taken before reached) {fuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx fuel reached stop after) (nonTimeout : stop ≠ .timeout) :
    length ≤ taken := by
  by_cases longer : length ≤ taken
  · exact longer
  · have bound : taken ≤ length := by omega
    obtain ⟨middle, leading, residual⟩ := known.split_length bound
    obtain ⟨remaining, _, same⟩ := leading.split_at (Nat.le_refl taken) steps
    have zero : remaining = 0 := by omega
    subst remaining
    rcases same.uncons with ⟨_, equal⟩ | ⟨rest, next, impossible, step, tail⟩
    · subst reached
      rcases residual.uncons with ⟨impossible, _⟩ | ⟨rest, next, _, step, tail⟩
      · omega
      · obtain ⟨stepFuel, actual⟩ := runtimeStep_demandInstructionStep step
        exact (stopped.excludes_step_nonTimeout nonTimeout actual).elim
    · omega
#print axioms DemandRuntimePrefix.length_le_stopped

#print axioms DemandRuntimePrefix.split_length

#print axioms DemandRuntimePrefix.split_at
end Goose.Lower
