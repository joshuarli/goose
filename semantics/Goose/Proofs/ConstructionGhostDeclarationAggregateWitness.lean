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

theorem aggregate_declaration_nonempty : ∃ mapped visits chunks continuation,
    OperandReplay (evalValue 39 config environment) 0 operands [] .initial mapped visits ∧
    (∀ visit ∈ visits, SourceHistory config 39 [4, 0, 0, visit.ordinal]
      (.value environment visit.operand) visit.before visit.outcome) ∧
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
  refine ⟨mapped, visits, chunks, continuation, replay, ?_, once, aligned, events, ?_⟩
  · simpa using children
  · simpa [ExecutionState.initial, ConstructionState.initial] using finalEq

#print axioms aggregate_declaration_nonempty
end Goose.Proofs.ConstructionGhostDeclarationAggregateWitness
