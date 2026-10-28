import Goose.Proofs.ConstructionInvocationReplay

namespace Goose.Proofs.ConstructionGhostInvocation
open Goose.Construct Goose.Proofs.ConstructionInvocationReplay

theorem visit_executes {action : α → EvalM β} {offset : Nat} {operands : List α}
    {accumulator : List β} {before : ExecutionState} {outcome : ExecutionStep (List β)}
    {visits : List (Invocation α β)}
    (replay : OperandReplay action offset operands accumulator before outcome visits)
    (visit : Invocation α β) (member : visit ∈ visits) :
    action visit.operand visit.before = visit.outcome := by
  induction replay with
  | done => simp at member
  | next head tail ih =>
    simp only [List.mem_cons] at member
    rcases member with same | later
    · subst visit; exact head
    · exact ih later
  | stopped head | escaped head | jumped head =>
    simp only [List.mem_singleton] at member
    subst visit
    exact head

#print axioms visit_executes
end Goose.Proofs.ConstructionGhostInvocation
