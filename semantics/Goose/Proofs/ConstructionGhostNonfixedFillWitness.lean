import Goose.Proofs.ConstructionGhostProtectedSourceEvents

namespace Goose.Proofs.ConstructionGhostNonfixedFillWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostDeclarationOnce Goose.Proofs.ConstructionGhostProtectedSourceEvents

private def element : Ty := .varr (.int .u8)
private def descriptor : LocalVar := ⟨"fill", .arr element 2, .immutable, 0, 0⟩
private def environment : RuntimeActivation := ⟨0, 4, #[descriptor], [(0, 1)], []⟩
private def implementation : Impl := ⟨"callee", #[], #[], #[], .mk 0 [] none, .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[], 0, #[], #[], #[]⟩⟩
private def operand : Expr := .bytes element [65, 66] 0
private def expression : Expr := .fill (.arr element 2) operand 0
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state
private def initial : ExecutionState := stepState (newDestination config.layout 4 descriptor.ty .value 0 none
  (producerCount? ⟨config.module, environment.vars⟩ expression) .initial)
private def ready : ExecutionState := stepState (liftConstruction 0 (renewReceivingDestination 0) initial)
private def sourceReady : ExecutionState := stepState (newDestination config.layout 4 element .value 0 none none ready)

theorem nonfixedFill_nonempty : ∃ sourceEvents continuation,
    SourceHistory config 38 [4, 0, 0, 0] (.builder environment 1 operand) sourceReady
      (buildExpr 38 config environment 1 operand sourceReady) ∧
    sourceEvents = [.write 1 0, .write 1 1] ∧
    (Goose.Proofs.Exit.stepState (execStmt 40 config environment (.letS 0 expression 0) .initial)).construction.events =
      sourceReady.construction.events ++ sourceEvents ++ continuation := by
  have occurrence : DeclarationOccurrence 39 config environment 0 expression 0 .initial (some 0) initial := by
    apply DeclarationOccurrence.direct descriptor (.local 4 1 0) .initial
      implementation .initial 0 initial
    all_goals first | exact DeclarationFallback.absent _ rfl | skip
    all_goals simp only [config, implementation, environment, descriptor, element, expression, operand, initial, stepState]
    all_goals cbv
  have renewed : liftConstruction 0 (renewReceivingDestination 0) initial = .ok 0 ready := by
    simp only [ready, initial, stepState, config, environment, descriptor, element, expression, operand]
    cbv
  have allocated : newDestination config.layout 4 element .value 0 none none ready = .ok 1 sourceReady := by
    simp only [sourceReady, ready, initial, stepState, config, environment, descriptor, element, expression, operand]
    cbv
  obtain ⟨history, execution, sourceEvents, continuation, sourceEq, finalEq⟩ :=
    nonfixedFill_declaration_sourceEvents 38 config environment [4, 0] 0 0 0 1 element 2 operand 0 0
      .initial initial ready sourceReady rfl occurrence renewed allocated
      (.legacy 38 (.builderBytes environment 1 element [65, 66] 0))
  have sourceActual : (Goose.Proofs.Exit.stepState (buildExpr 38 config environment 1 operand sourceReady)).construction.events =
      sourceReady.construction.events ++ [.write 1 0, .write 1 1] := by
    simp only [sourceReady, ready, initial, stepState, config, environment, descriptor, element, expression, operand]
    cbv
  have sourceEventsEq : sourceEvents = [.write 1 0, .write 1 1] :=
    (List.append_right_inj _).mp (sourceEq.symm.trans sourceActual)
  exact ⟨sourceEvents, continuation, history, sourceEventsEq, finalEq⟩

theorem nonfixedFill_succeeds :
    execStmt 40 config environment (.letS 0 expression 0) .initial =
      .ok (.normal .unit) (stepState (execStmt 40 config environment (.letS 0 expression 0) .initial)) := by
  simp only [stepState, config, implementation, environment, descriptor, element, expression, operand]
  cbv

#print axioms nonfixedFill_succeeds
#print axioms nonfixedFill_nonempty
end Goose.Proofs.ConstructionGhostNonfixedFillWitness
