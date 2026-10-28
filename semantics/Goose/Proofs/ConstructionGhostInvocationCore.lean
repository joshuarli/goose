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

theorem structLiteral_replay (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (id : Goose.Core.StructId) (fields : TyList) (operands : List Expr) (before : ExecutionState) :
    ∃ mapped visits,
      OperandReplay (evalValue fuel config environment) 0 operands [] before mapped visits ∧
      evalValue (fuel + 1) config environment (.structLit (.structT id fields) operands) before =
        match mapped with
        | .ok values after => .ok (.record id values.toArray) after
        | .stop reason after => .stop reason after
        | .escape address carriers after => .escape address carriers after
        | .jump target kind after => .jump target kind after := by
  obtain ⟨visits, replay⟩ := mapM_replay (evalValue fuel config environment) operands before
  refine ⟨_, visits, replay, ?_⟩
  simp only [evalValue, bind, pure]
  cases (operands.mapM (evalValue fuel config environment)) before <;> rfl

#print axioms structLiteral_replay
#print axioms visit_executes
end Goose.Proofs.ConstructionGhostInvocation
