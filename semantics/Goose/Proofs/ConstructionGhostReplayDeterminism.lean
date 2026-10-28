import Goose.Proofs.ConstructionInvocationReplay

namespace Goose.Proofs.ConstructionGhostReplayDeterminism
open Goose.Construct Goose.Proofs.ConstructionInvocationReplay

theorem operandReplay_deterministic {action : α → EvalM β} {offset : Nat} {operands : List α}
    {accumulator : List β} {before : ExecutionState} {first second : ExecutionStep (List β)}
    {firstVisits secondVisits : List (Invocation α β)}
    (left : OperandReplay action offset operands accumulator before first firstVisits)
    (right : OperandReplay action offset operands accumulator before second secondVisits) :
    first = second ∧ firstVisits = secondVisits := by
  induction left generalizing second secondVisits with
  | done => cases right; exact ⟨rfl, rfl⟩
  | next head tail ih =>
      cases right <;> simp_all
      exact ih (by assumption)
  | stopped head => cases right <;> simp_all
  | escaped head => cases right <;> simp_all
  | jumped head => cases right <;> simp_all

#print axioms operandReplay_deterministic
end Goose.Proofs.ConstructionGhostReplayDeterminism
