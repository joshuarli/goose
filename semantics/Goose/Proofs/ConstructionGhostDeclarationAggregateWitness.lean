import Goose.Proofs.ConstructionGhostDeclarationAggregateEvents

namespace Goose.Proofs.ConstructionGhostDeclarationAggregateWitness
open Goose.Construct Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostInvocation
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostInvocationEventChunks Goose.Proofs.ConstructionGhostDeclarationOnce
open Goose.Proofs.ConstructionGhostDeclarationAggregateEvents

private def descriptor : LocalVar := ⟨"aggregate", .arr .unit 2, .immutable, 0, 0⟩
private def environment : RuntimeActivation := ⟨0, 4, #[descriptor], [(0, 1)], []⟩
private def bytes : Expr := .bytes (.varr (.int .u8)) [65, 66] 0
private def context : Context := ⟨0, "source", [], [], []⟩
private def implementation : Impl := ⟨"source", #[], #[], #[], .mk 0 [.expr bytes 0] none, .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def operand : Expr := .call 0 [] 0
private def operands : List Expr := [operand, operand]
private def expression : Expr := .arrLit (.arr .unit 2) operands 0

private theorem replay_success_length {action : α → EvalM β} {offset : Nat} {operands : List α}
    {accumulator : List β} {before : ExecutionState} {outcome : ExecutionStep (List β)} {visits : List (Invocation α β)}
    (replay : OperandReplay action offset operands accumulator before outcome visits)
    (success : ∃ values after, outcome = .ok values after) : visits.length = operands.length := by
  induction replay with
  | done => rfl
  | next head tail ih => simpa using ih success
  | stopped | escaped | jumped => simp_all

private theorem aligned_length {visits : List (Invocation α β)} {chunks : List (List Goose.Core.ConstructionEvent)}
    (aligned : ChunksAlign visits chunks) : visits.length = chunks.length := by
  induction aligned with
  | nil => rfl
  | cons visit chunk visits chunks events tail ih => simpa only [List.length_cons] using congrArg Nat.succ ih

theorem aggregate_declaration_nonempty : ∃ mapped visits chunks continuation,
    OperandReplay (evalValue 39 config environment) 0 operands [] .initial mapped visits ∧
    (∀ visit ∈ visits, SourceHistory config 39 [4, 0, 0, visit.ordinal]
      (.value environment visit.operand) visit.before visit.outcome) ∧
    visits.length = 2 ∧ chunks.length = 2 ∧ visits.map Invocation.ordinal = [0, 1] ∧
    (visits.map Invocation.ordinal).Nodup ∧ ChunksAlign visits chunks ∧
    chunks.flatten = [.begin 0, .write 0 0, .write 0 1, .publish 0,
      .begin 1, .write 1 0, .write 1 1, .publish 1] ∧
    (Goose.Proofs.Exit.stepState (execStmt 41 config environment (.letS 0 expression 0) .initial)).construction.events =
      chunks.flatten ++ continuation := by
  have occurrence : DeclarationOccurrence 40 config environment 0 expression 0 .initial none .initial := by
    apply DeclarationOccurrence.fixed descriptor (.local 4 1 0) .initial
    · rfl
    · rfl
    · simp [rootOf, environment, descriptor, bind, pure]
  have supported : ∀ operand ∈ operands, FuelSupport config 39 (.value environment operand) := by
    intro child member
    simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at member
    have body : ∀ environment, SupportedOperation config (.statements environment [.expr bytes 0]) := by
      intro environment
      exact .sequence environment (.expression environment 0 (.valueBytes environment (.varr (.int .u8)) [65, 66] 0)) (.empty environment)
    have callee : SupportedOperation config (.call environment 0 0) := by
      apply SupportedOperation.call environment 0 0 context implementation
      · rfl
      · rfl
      · rfl
      · rfl
      · intro act
        exact .activation _ 0 _ 0 body
    rcases member with rfl | rfl <;> exact .legacy 39 (.valueCall environment 0 0 context implementation rfl rfl rfl callee)
  have shape : ValueAggregate expression operands := .fixedArray (.arr .unit 2) operands 0 rfl
  obtain ⟨mapped, visits, chunks, continuation, replay, children, ordered, once, aligned, sourceEvents, finalEq⟩ :=
    aggregate_declaration_sourceEvents 39 config environment [4, 0] 0 expression operands 0 .initial .initial shape occurrence supported
  obtain ⟨other, otherVisits, otherReplay, _, _, _, valueEq, _⟩ :=
    Goose.Proofs.ConstructionGhostSourceAggregate.aggregate_fuelReplay 39 config environment [4, 0, 0]
      expression operands .initial shape supported
  have mappedEq : other = mapped := otherReplay.execute.symm.trans replay.execute
  rw [mappedEq] at valueEq
  have actualValue : ∃ after, evalValue 40 config environment expression .initial = .ok (.fixed #[.unit, .unit]) after := by
    let after := Goose.Proofs.Exit.stepState (evalValue 40 config environment expression .initial)
    refine ⟨after, ?_⟩
    simp only [after, config, environment, descriptor, expression, operands, operand, implementation, context, bytes]
    unfold evalValue
    cbv
    unfold evalValue
    cbv
    unfold evalValue
    cbv
  obtain ⟨after, actualValue⟩ := actualValue
  rw [valueEq] at actualValue
  have complete : visits.length = 2 := by
    cases mapped with
    | ok values state => simpa [operands] using replay_success_length replay ⟨values, state, rfl⟩
    | stop reason state => simp [Goose.Proofs.ConstructionGhostSourceAggregate.aggregateResult] at actualValue
    | escape address carriers state => simp [Goose.Proofs.ConstructionGhostSourceAggregate.aggregateResult] at actualValue
    | jump target kind state => simp [Goose.Proofs.ConstructionGhostSourceAggregate.aggregateResult] at actualValue
  have actual : (Goose.Proofs.Exit.stepState (evalValue 40 config environment expression .initial)).construction.events =
      [.begin 0, .write 0 0, .write 0 1, .publish 0, .begin 1, .write 1 0, .write 1 1, .publish 1] := by
    simp only [config, environment, descriptor, expression, operands, operand, implementation, context, bytes]
    unfold evalValue
    cbv
    unfold evalValue
    cbv
    unfold evalValue
    cbv
  rw [actual] at sourceEvents
  have events : chunks.flatten = [.begin 0, .write 0 0, .write 0 1, .publish 0,
      .begin 1, .write 1 0, .write 1 1, .publish 1] := by
    simpa [ExecutionState.initial, ConstructionState.initial] using sourceEvents.symm
  have chunkCount : chunks.length = 2 := by
    have equal := aligned_length aligned
    omega
  have ordinals : visits.map Invocation.ordinal = [0, 1] := by
    have actual := replay.ordinals
    rw [complete] at actual
    exact actual
  refine ⟨mapped, visits, chunks, continuation, replay, ?_, complete, chunkCount, ordinals, once, aligned, events, ?_⟩
  · simpa using children
  · simpa [ExecutionState.initial, ConstructionState.initial] using finalEq

#print axioms aggregate_declaration_nonempty
end Goose.Proofs.ConstructionGhostDeclarationAggregateWitness
