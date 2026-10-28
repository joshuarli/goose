import Goose.Lower.DemandRunAtPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem DemandRuntimePrefix.compare_strict {cx : FnCtx} {expectedLength actualLength : Nat}
    {start expectedEnd actualEnd : DemandRuntimePoint}
    (expected : DemandRuntimePrefix cx expectedLength start expectedEnd)
    (actual : DemandRuntimePrefix cx actualLength start actualEnd) :
    (∃ rest, expectedLength + rest = actualLength ∧ DemandRuntimePrefix cx rest expectedEnd actualEnd) ∨
    (∃ rest, 0 < rest ∧ actualLength + rest = expectedLength ∧ DemandRuntimePrefix cx rest actualEnd expectedEnd) := by
  induction expected generalizing actualLength actualEnd with
  | zero => exact Or.inl ⟨_, by simp, actual⟩
  | @next length start middle expectedEnd expectedStep expectedTail ih =>
    rcases actual.uncons with ⟨rfl, rfl⟩ | ⟨actualTailLength, actualMiddle, rfl, actualStep, actualTail⟩
    · exact Or.inr ⟨length + 1, by omega, by simp, .next expectedStep expectedTail⟩
    · obtain ⟨expectedFuel, expectedInstruction⟩ := runtimeStep_demandInstructionStep expectedStep
      obtain ⟨actualFuel, actualInstruction⟩ := runtimeStep_demandInstructionStep actualStep
      have equal := expectedInstruction.deterministic_across_fuel actualInstruction
      have equalPoints : middle = actualMiddle := by
        cases middle
        cases actualMiddle
        exact equal
      subst actualMiddle
      rcases ih actualTail with ⟨rest, count, tail⟩ | ⟨rest, positive, count, tail⟩
      · exact Or.inl ⟨rest, by omega, tail⟩
      · exact Or.inr ⟨rest, positive, by omega, tail⟩


theorem DemandRuntimePrefix.compare {cx : FnCtx} {expectedLength actualLength : Nat}
    {start expectedEnd actualEnd : DemandRuntimePoint}
    (expected : DemandRuntimePrefix cx expectedLength start expectedEnd)
    (actual : DemandRuntimePrefix cx actualLength start actualEnd) :
    (∃ rest, expectedLength + rest = actualLength ∧ DemandRuntimePrefix cx rest expectedEnd actualEnd) ∨
    (∃ rest, actualLength + rest = expectedLength ∧ DemandRuntimePrefix cx rest actualEnd expectedEnd) := by
  rcases expected.compare_strict actual with first | ⟨rest, _, count, suffix⟩
  · exact Or.inl first
  · exact Or.inr ⟨rest, count, suffix⟩

theorem DemandRuntimePrefix.compare_stopped {cx : FnCtx} {expectedLength actualLength fuel : Nat}
    {start expectedEnd actualEnd : DemandRuntimePoint} {stop : Stop} {after : St}
    (expected : DemandRuntimePrefix cx expectedLength start expectedEnd)
    (actual : DemandRuntimePrefix cx actualLength start actualEnd)
    (stopped : DemandInstructionStop cx fuel actualEnd stop after) (nonTimeout : stop ≠ .timeout) :
    ∃ rest, expectedLength + rest = actualLength ∧ DemandRuntimePrefix cx rest expectedEnd actualEnd := by
  rcases expected.compare actual with longer | ⟨rest, count, suffix⟩
  · exact longer
  · cases suffix with
    | zero => exact ⟨0, by omega, .zero _⟩
    | next step tail =>
      obtain ⟨stepFuel, first⟩ := runtimeStep_demandInstructionStep step
      exact (stopped.excludes_step_nonTimeout nonTimeout first).elim

#print axioms DemandRuntimePrefix.compare_strict
#print axioms DemandRuntimePrefix.compare
#print axioms DemandRuntimePrefix.compare_stopped
end Goose.Lower
