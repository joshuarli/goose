import Goose.Proofs.ConstructionGhostDeclarationFallback

namespace Goose.Proofs.ConstructionGhostDeclarationFallbackWitness
open Goose.Construct Goose.Proofs.ConstructionGhostNonfixedDeclaration Goose.Proofs.ConstructionGhostDeclarationFallback

private def expression : Expr := .bytes (.varr (.int .u8)) [65, 66] 0
private def descriptor : LocalVar := ⟨"x", .varr (.int .u8), .immutable, 0, 0⟩
private def result : ResultDescriptor := ⟨.varr (.int .u8), .value, some 0⟩
private def implementation : Impl := ⟨"entry", #[], #[result], #[descriptor], .mk 0 [] none, .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 4, #[descriptor], [(0, 1)], [.construct 0]⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state
private def base : ExecutionState := stepState (newDestination config.layout 4 descriptor.ty .elementRun 0 none (some 2) .initial)
private def selectedReady : ExecutionState := stepState (liftConstruction 0 (renewReceivingDestination 0) base)
private def pending : PendingDestination := (selectedReady.construction.destinations[0]?).get (by
  simp only [selectedReady, base, stepState, config, descriptor, implementation, result, expression]
  cbv)
private def destinationReady : ExecutionState := stepState (getDestination 0 selectedReady)

theorem nonvalueFallback_executes : ∃ after,
    newDestination config.layout 4 descriptor.ty .elementRun 0 none (some 2) .initial = .ok 0 base ∧
    pending.capability.request = .elementRun ∧
    execStmt 39 config environment (.letS 0 expression 0) base = .ok (.normal .unit) after ∧
    execStmt 39 config environment (.letS 0 expression 0) base =
      declarationAfterMaterialization 38 config environment descriptor (.local 4 1 0) expression 0
        (materializeProducer 38 ⟨config.module, environment.vars⟩ expression
          (evalValue 38 config environment expression) destinationReady) ∧
    after.construction.events = [.begin 0, .begin 1, .write 1 0, .write 1 1, .publish 1] := by
  have root : rootOf environment 0 base = .ok (.local 4 1 0) base := by
    simp only [rootOf, environment, descriptor]
    cbv
  have selected : liftConstruction 0 (renewReceivingDestination 0) base = .ok 0 selectedReady := by
    simp only [selectedReady, base, stepState, config, descriptor, implementation, result, expression]
    cbv
  have pendingFound : getDestination 0 selectedReady = .ok pending destinationReady := by
    simp only [destinationReady, pending, selectedReady, base, stepState, config, descriptor, implementation, result, expression]
    cbv
  have request : pending.capability.request = .elementRun := by
    simp only [pending, selectedReady, base, stepState, config, descriptor, implementation, result, expression]
    cbv
  have fallback := nonfixedDeclaration_nonvalueFallback 38 config environment 0 expression 0 base base selectedReady destinationReady
    descriptor (.local 4 1 0) implementation result 0 0 0 pending rfl rfl root rfl rfl rfl selected pendingFound (by rw [request]; decide)
  refine ⟨stepState (execStmt 39 config environment (.letS 0 expression 0) base), ?_, request, ?_, fallback, ?_⟩
  · simp only [base, stepState, config, descriptor, implementation, result, expression]
    cbv
  · simp only [stepState, config, environment, expression, descriptor, implementation, result, base]
    cbv
  · simp only [stepState, config, environment, expression, descriptor, implementation, result, base]
    cbv

#print axioms nonvalueFallback_executes
end Goose.Proofs.ConstructionGhostDeclarationFallbackWitness
