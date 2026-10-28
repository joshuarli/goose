import Goose.Proofs.ConstructionGhostNamedDeclarationEvents

namespace Goose.Proofs.ConstructionGhostNamedDeclarationEventsWitness
open Goose.Construct Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostSourceFuel Goose.Proofs.ConstructionGhostNamedDeclarationEvents

private def expression : Expr := .bytes (.varr (.int .u8)) [65, 66] 0
private def descriptor : LocalVar := ⟨"x", .varr (.int .u8), .immutable, 0, 0⟩
private def result : ResultDescriptor := ⟨.varr (.int .u8), .value, some 0⟩
private def statement : Stmt := .letS 0 expression 0
private def implementation : Impl := ⟨"entry", #[], #[result], #[descriptor], .mk 0 [] none, .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 4, #[descriptor], [(0, 1)], [.construct 0]⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state
private def base : ExecutionState := stepState (newDestination config.layout 4 descriptor.ty .value 0 none (some 2) .initial)
private def selectedReady : ExecutionState := stepState (liftConstruction 0 (renewReceivingDestination 0) base)
private def pending : PendingDestination := (selectedReady.construction.destinations[0]?).get (by
  simp only [selectedReady, base, stepState, config, environment, descriptor, implementation, result, expression]
  cbv)
private def destinationReady : ExecutionState := stepState (getDestination 0 selectedReady)
private def renewedReady : ExecutionState := stepState (liftConstruction 0 (renewReceivingDestination 0) destinationReady)
private def buildReady : ExecutionState := stepState (liftConstruction 0 (prepareNamedBinding 0 descriptor.ty) renewedReady)

theorem namedInitializer_sourceEvents : ∃ after visits,
    StatementReplay config environment 40 0 [statement] base (.ok (.normal .unit) after) visits ∧
    (∃ visit ∈ visits,
      SourceHistory config 38 [environment.act, visit.ordinal, 0] (.builder environment 0 expression) buildReady
        (buildExpr 38 config environment 0 expression buildReady) ∧
      Goose.Proofs.ConstructionExecution.EventPrefix
        (Goose.Proofs.Exit.stepState (buildExpr 38 config environment 0 expression buildReady)).construction.events
        (Goose.Proofs.Exit.stepState visit.outcome).construction.events) ∧
    (Goose.Proofs.Exit.stepState (buildExpr 38 config environment 0 expression buildReady)).construction.events =
      [.begin 0, .write 0 0, .write 0 1] ∧
    after.construction.events = [.begin 0, .write 0 0, .write 0 1] := by
  let after := stepState (execStmt 39 config environment statement base)
  have actual : execStmt 39 config environment statement base = .ok (.normal .unit) after := by
    simp only [after, stepState, config, environment, statement, expression, descriptor, implementation, result, base]
    cbv
  have builtEvents : (Goose.Proofs.Exit.stepState (buildExpr 38 config environment 0 expression buildReady)).construction.events =
      [.begin 0, .write 0 0, .write 0 1] := by
    simp only [buildReady, renewedReady, destinationReady, selectedReady, base, stepState, config, descriptor, expression, implementation, result]
    cbv
  have events : after.construction.events = [.begin 0, .write 0 0, .write 0 1] := by
    simp only [after, stepState, config, environment, statement, expression, descriptor, implementation, result, base]
    cbv
  let visit : StatementInvocation := ⟨environment.act, 0, 39, statement, base, .ok (.normal .unit) after⟩
  have replay : StatementReplay config environment 40 0 [statement] base (.ok (.normal .unit) after) [visit] :=
    .next actual (.done 38 1 after)
  have root : rootOf environment 0 base = .ok (.local 4 1 0) base := by
    simp only [rootOf, environment, descriptor]
    cbv
  have selected : liftConstruction 0 (renewReceivingDestination 0) base = .ok 0 selectedReady := by
    simp only [selectedReady, base, stepState, config, descriptor, implementation, result, expression]
    cbv
  have pendingFound : getDestination 0 selectedReady = .ok pending destinationReady := by
    simp only [destinationReady, pending, selectedReady, base, stepState, config, descriptor, implementation, result, expression]
    cbv
  have request : pending.capability.request = .value := by
    simp only [pending, selectedReady, base, stepState, config, descriptor, implementation, result, expression]
    cbv
  have renewed : liftConstruction 0 (renewReceivingDestination 0) destinationReady = .ok 0 renewedReady := by
    simp only [renewedReady, destinationReady, selectedReady, base, stepState, config, descriptor, implementation, result, expression]
    cbv
  have prepared : liftConstruction 0 (prepareNamedBinding 0 descriptor.ty) renewedReady = .ok () buildReady := by
    simp only [buildReady, renewedReady, destinationReady, selectedReady, base, stepState, config, descriptor, implementation, result, expression]
    cbv
  obtain ⟨history, retained⟩ := namedDeclaration_visit_sourceEvents replay visit (by simp [visit])
    38 0 expression 0 base selectedReady destinationReady renewedReady buildReady descriptor (.local 4 1 0) implementation
    result 0 0 0 0 pending rfl rfl rfl rfl root rfl rfl rfl selected pendingFound request renewed prepared
    (.legacy 38 (.builderBytes environment 0 (.varr (.int .u8)) [65, 66] 0))
  exact ⟨after, [visit], replay, ⟨visit, by simp, history, retained⟩, builtEvents, events⟩

#print axioms namedInitializer_sourceEvents
end Goose.Proofs.ConstructionGhostNamedDeclarationEventsWitness
