import Goose.Proofs.ConstructionGhostDeclarationFillEvents

namespace Goose.Proofs.ConstructionGhostDeclarationFillWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostDeclarationOnce Goose.Proofs.ConstructionGhostDeclarationFillEvents

private def descriptor : LocalVar := ⟨"fill", .arr .unit 3, .immutable, 0, 0⟩
private def environment : RuntimeActivation := ⟨0, 4, #[descriptor], [(0, 1)], []⟩
private def bytes : Expr := .bytes (.varr (.int .u8)) [65, 66] 0
private def context : Context := ⟨0, "source", [], [], []⟩
private def implementation : Impl := ⟨"source", #[], #[], #[], .mk 0 [.expr bytes 0] none, .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def operand : Expr := .call 0 [] 0
private def expression : Expr := .fill (.arr .unit 3) operand 0

private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem supported : FuelSupport config 39 (.value environment operand) := by
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
  exact .legacy 39 (.valueCall environment 0 0 context implementation rfl rfl rfl callee)

theorem fill_declaration_nonempty : ∃ source continuation,
    SourceHistory config 39 [4, 0, 0, 0] (.value environment operand) .initial
      (evalValue 39 config environment operand .initial) ∧
    source = [.begin 0, .write 0 0, .write 0 1, .publish 0] ∧
    evalValue 40 config environment expression .initial =
      .ok (.fixed #[.unit, .unit, .unit]) (stepState (evalValue 40 config environment expression .initial)) ∧
    (Goose.Proofs.Exit.stepState (execStmt 41 config environment (.letS 0 expression 0) .initial)).construction.events =
      source ++ continuation := by
  have occurrence : DeclarationOccurrence 40 config environment 0 expression 0 .initial none .initial := by
    apply DeclarationOccurrence.fixed descriptor (.local 4 1 0) .initial
    · rfl
    · rfl
    · simp [rootOf, environment, descriptor, bind, pure]
  obtain ⟨history, execution, source, continuation, sourceEq, finalEq⟩ := fixedFill_declaration_sourceEvents
    39 config environment [4, 0] 0 .unit 3 operand 0 0 .initial .initial rfl occurrence
      supported
  have actual : (Goose.Proofs.Exit.stepState (evalValue 39 config environment operand .initial)).construction.events =
      [.begin 0, .write 0 0, .write 0 1, .publish 0] := by
    simp only [config, environment, descriptor, operand, implementation, context, bytes]
    unfold evalValue
    cbv
    unfold evalValue
    cbv
  rw [actual] at sourceEq
  have events : source = [.begin 0, .write 0 0, .write 0 1, .publish 0] := by
    simpa [ExecutionState.initial, ConstructionState.initial] using sourceEq.symm
  refine ⟨source, continuation, ?_, events, ?_, ?_⟩
  · simpa using history
  · simp only [stepState, config, environment, descriptor, operand, implementation, context, bytes, expression]
    unfold evalValue
    cbv
    unfold evalValue
    cbv
  · simpa [ExecutionState.initial, ConstructionState.initial, expression] using finalEq

#print axioms fill_declaration_nonempty
end Goose.Proofs.ConstructionGhostDeclarationFillWitness
