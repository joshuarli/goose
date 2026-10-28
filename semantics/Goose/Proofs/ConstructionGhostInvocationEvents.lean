import Goose.Proofs.ConstructionGhostSourceTrace

namespace Goose.Proofs.ConstructionGhostInvocationEvents
open Goose.Construct Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostInvocation
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceAggregate
open Goose.Proofs.ConstructionGhostSourceTrace Goose.Proofs.ConstructionExecution

inductive InvocationEvents : List Goose.Core.ConstructionEvent → List (Invocation α β) → List Goose.Core.ConstructionEvent → Prop
  | done (events : List Goose.Core.ConstructionEvent) : InvocationEvents events [] events
  | next (visit : Invocation α β) (rest : List (Invocation α β)) (after : List Goose.Core.ConstructionEvent)
      (segment : EventPrefix visit.before.construction.events (Goose.Proofs.Exit.stepState visit.outcome).construction.events)
      (remaining : InvocationEvents (Goose.Proofs.Exit.stepState visit.outcome).construction.events rest after) :
      InvocationEvents visit.before.construction.events (visit :: rest) after

theorem replay_invocationEvents (replay : OperandReplay action offset operands accumulator before outcome visits)
    (preserved : ∀ operand, KeepsEventPrefix (action operand)) :
    InvocationEvents before.construction.events visits (Goose.Proofs.Exit.stepState outcome).construction.events := by
  induction replay with
  | done => exact .done _
  | @next offset operand rest accumulator before middle value outcome visits head tail ih =>
      have segment := preserved operand before
      rw [head] at segment
      exact .next ⟨offset, operand, before, .ok value middle⟩ visits _ segment ih
  | @stopped offset operand rest accumulator before after reason head =>
      have segment := preserved operand before
      rw [head] at segment
      exact .next ⟨offset, operand, before, .stop reason after⟩ [] _ segment (.done _)
  | @escaped offset operand rest accumulator before after address carriers head =>
      have segment := preserved operand before
      rw [head] at segment
      exact .next ⟨offset, operand, before, .escape address carriers after⟩ [] _ segment (.done _)
  | @jumped offset operand rest accumulator before after target kind head =>
      have segment := preserved operand before
      rw [head] at segment
      exact .next ⟨offset, operand, before, .jump target kind after⟩ [] _ segment (.done _)

theorem aggregate_invocationEvents (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (expression : Expr) (operands : List Expr) (before : ExecutionState)
    (shape : ValueAggregate expression operands)
    (supported : ∀ operand ∈ operands, SupportedOperation config (.value environment operand)) :
    ∃ mapped visits,
      OperandReplay (evalValue fuel config environment) 0 operands [] before mapped visits ∧
      (∀ visit ∈ visits, SourceHistory config fuel (path ++ [visit.ordinal])
        (.value environment visit.operand) visit.before visit.outcome) ∧
      visits.map Invocation.operand = operands.take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧
      InvocationEvents before.construction.events visits
        (Goose.Proofs.Exit.stepState (evalValue (fuel + 1) config environment expression before)).construction.events := by
  obtain ⟨mapped, visits, replay, children, ordered, once, execution, history⟩ :=
    aggregate_replay fuel config environment path expression operands before shape supported
  have segments := replay_invocationEvents replay (fun operand => (evaluation_keepsEventPrefix fuel config).value environment operand)
  refine ⟨mapped, visits, replay, children, ordered, once, ?_⟩
  rw [execution]
  cases shape <;> cases mapped <;> exact segments

#print axioms replay_invocationEvents
#print axioms aggregate_invocationEvents
end Goose.Proofs.ConstructionGhostInvocationEvents
