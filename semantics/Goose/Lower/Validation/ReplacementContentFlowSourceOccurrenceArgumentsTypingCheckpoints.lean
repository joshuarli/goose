import Goose.Lower.Validation.SummaryPreservationReplayArgumentSource

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound SummaryPreservation

theorem tyArgs_argument_checkpoint {env : TEnv} {callee : Impl} {parameters : List Param}
    {earlier later : List Arg} {argument : Arg} {start finish : Nat}
    (arity : parameters.length = (earlier ++ argument :: later).length)
    (typed : tyArgs env callee parameters (earlier ++ argument :: later) start = .ok ((), finish)) :
    ∃ earlierParameters parameter laterParameters childStart childFinish,
      parameters = earlierParameters ++ parameter :: laterParameters ∧
      earlierParameters.length = earlier.length ∧
      ArgumentTyping env argument childStart childFinish ∧
      tyArgs env callee (parameter :: laterParameters) (argument :: later) childStart =
        .ok ((), finish) ∧
      tyArgs env callee laterParameters later childFinish = .ok ((), finish) := by
  induction earlier generalizing parameters start with
  | nil =>
    cases parameters with
    | nil => simp at arity
    | cons parameter rest =>
      obtain ⟨middle, child, remaining⟩ := tyArgs_cons_children typed
      exact ⟨[], parameter, rest, start, middle, rfl, rfl, child, typed, remaining⟩
  | cons first rest ih =>
    cases parameters with
    | nil => simp at arity
    | cons parameter parameters =>
      obtain ⟨middle, _, remaining⟩ := tyArgs_cons_children typed
      obtain ⟨earlierParameters, selected, laterParameters, childStart, childFinish,
        split, length, child, selectedTyped, suffixTyped⟩ :=
        ih (by simpa using arity) remaining
      exact ⟨parameter :: earlierParameters, selected, laterParameters, childStart, childFinish,
        by simp [split], by simp [length], child, selectedTyped, suffixTyped⟩

#print axioms tyArgs_argument_checkpoint

end Goose.Lower.Validation.ReplacementContentFlowSource
