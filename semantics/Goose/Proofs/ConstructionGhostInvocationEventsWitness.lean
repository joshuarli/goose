import Goose.Proofs.ConstructionGhostInvocationEvents

namespace Goose.Proofs.ConstructionGhostInvocationEventsWitness
open Goose.Construct Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostInvocation
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostInvocationEvents
open Goose.Proofs.ConstructionExecution

private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def operand : Expr := .bytes (.varr (.int .u8)) [65, 66] 0
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state
private def stepValue : ExecutionStep Value → Value
  | .ok value _ => value
  | _ => .unit

theorem byteInvocation_events : ∃ value after visits,
    evalValue 20 config environment operand .initial = .ok value after ∧
    OperandReplay (evalValue 20 config environment) 0 [operand] [] .initial (.ok [value] after) visits ∧
    (∀ visit ∈ visits, SourceHistory config 20 [visit.ordinal] (.value environment visit.operand) visit.before visit.outcome) ∧
    InvocationEvents [] visits after.construction.events ∧
    after.construction.events = [.begin 0, .write 0 0, .write 0 1, .publish 0] := by
  let outcome := evalValue 20 config environment operand .initial
  let value := stepValue outcome
  let after := stepState outcome
  have actual : evalValue 20 config environment operand .initial = .ok value after := by
    unfold value after outcome stepValue stepState config environment operand
    unfold evalValue
    cbv
  have events : after.construction.events = [.begin 0, .write 0 0, .write 0 1, .publish 0] := by
    unfold after outcome stepState config environment operand
    unfold evalValue
    cbv
  let visit : Invocation Expr Value := ⟨0, operand, .initial, .ok value after⟩
  have replay : OperandReplay (evalValue 20 config environment) 0 [operand] [] .initial (.ok [value] after) [visit] :=
    .next actual (.done 1 [value] after)
  have source : SourceHistory config 20 [0] (.value environment operand) .initial (.ok value after) := by
    have history := history_exists 20 config (.value environment operand) [0] .initial
      (.valueBytes environment (.varr (.int .u8)) [65, 66] 0)
    simp only [execute] at history
    rw [actual] at history
    exact history
  have segments := replay_invocationEvents replay (fun expression => (evaluation_keepsEventPrefix 20 config).value environment expression)
  refine ⟨value, after, [visit], actual, replay, ?_, segments, events⟩
  intro selected member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst selected
  exact source

#print axioms byteInvocation_events
end Goose.Proofs.ConstructionGhostInvocationEventsWitness
