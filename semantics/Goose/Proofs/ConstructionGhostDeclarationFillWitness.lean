import Goose.Proofs.ConstructionGhostDeclarationFillEvents

namespace Goose.Proofs.ConstructionGhostDeclarationFillWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostDeclarationOnce Goose.Proofs.ConstructionGhostDeclarationFillEvents

private def descriptor : LocalVar := ⟨"fill", .arr .unit 3, .immutable, 0, 0⟩
private def environment : RuntimeActivation := ⟨0, 4, #[descriptor], [(0, 1)], []⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩⟩
private def operand : Expr := .bytes (.varr (.int .u8)) [65, 66] 0
private def expression : Expr := .fill (.arr .unit 3) operand 0

theorem fill_declaration_nonempty : ∃ source continuation,
    SourceHistory config 39 [4, 0, 0, 0] (.value environment operand) .initial
      (evalValue 39 config environment operand .initial) ∧
    source = [.begin 0, .write 0 0, .write 0 1, .publish 0] ∧
    (Goose.Proofs.Exit.stepState (execStmt 41 config environment (.letS 0 expression 0) .initial)).construction.events =
      source ++ continuation := by
  have occurrence : DeclarationOccurrence 40 config environment 0 expression 0 .initial none .initial := by
    apply DeclarationOccurrence.fixed descriptor (.local 4 1 0) .initial
    · rfl
    · rfl
    · simp [rootOf, environment, descriptor, bind, pure]
  obtain ⟨history, execution, source, continuation, sourceEq, finalEq⟩ := fixedFill_declaration_sourceEvents
    39 config environment [4, 0] 0 .unit 3 operand 0 0 .initial .initial rfl occurrence
      (.legacy 39 (.valueBytes environment (.varr (.int .u8)) [65, 66] 0))
  have actual : (Goose.Proofs.Exit.stepState (evalValue 39 config environment operand .initial)).construction.events =
      [.begin 0, .write 0 0, .write 0 1, .publish 0] := by
    simp only [config, environment, descriptor, operand]
    unfold evalValue
    cbv
  rw [actual] at sourceEq
  have events : source = [.begin 0, .write 0 0, .write 0 1, .publish 0] := by
    simpa [ExecutionState.initial, ConstructionState.initial] using sourceEq.symm
  refine ⟨source, continuation, ?_, events, ?_⟩
  · simpa using history
  · simpa [ExecutionState.initial, ConstructionState.initial, expression] using finalEq

#print axioms fill_declaration_nonempty
end Goose.Proofs.ConstructionGhostDeclarationFillWitness
