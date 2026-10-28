import Goose.Proofs.ConstructionGhostDirectDeclarationEvents

namespace Goose.Proofs.ConstructionGhostDirectDeclarationEventsWitness
open Goose.Construct Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostSourceFuel Goose.Proofs.ConstructionGhostDirectDeclarationEvents

private def expression : Expr := .bytes (.varr (.int .u8)) [65, 66] 0
private def descriptor : LocalVar := ⟨"x", .varr (.int .u8), .immutable, 0, 0⟩
private def statement : Stmt := .letS 0 expression 0
private def implementation : Impl := ⟨"entry", #[], #[], #[descriptor], .mk 0 [] none, .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 4, #[descriptor], [(0, 1)], []⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem directInitializer_sourceEvents : ∃ after buildReady visits,
    StatementReplay config environment 40 0 [statement] .initial (.ok (.normal .unit) after) visits ∧
    newDestination config.layout environment.act descriptor.ty .value 0 none (some 2) .initial = .ok 0 buildReady ∧
    (∃ visit ∈ visits,
      SourceHistory config 38 [environment.act, visit.ordinal, 0] (.builder environment 0 expression) buildReady
        (buildExpr 38 config environment 0 expression buildReady) ∧
      Goose.Proofs.ConstructionExecution.EventPrefix
        (Goose.Proofs.Exit.stepState (buildExpr 38 config environment 0 expression buildReady)).construction.events
        (Goose.Proofs.Exit.stepState visit.outcome).construction.events) ∧
    (Goose.Proofs.Exit.stepState (buildExpr 38 config environment 0 expression buildReady)).construction.events =
      [.begin 0, .write 0 0, .write 0 1] ∧
    after.construction.events = [.begin 0, .write 0 0, .write 0 1, .publish 0] := by
  let after := stepState (execStmt 39 config environment statement .initial)
  let buildReady := stepState (newDestination config.layout environment.act descriptor.ty .value 0 none (some 2) .initial)
  have actual : execStmt 39 config environment statement .initial = .ok (.normal .unit) after := by
    unfold after stepState config environment statement expression descriptor implementation
    cbv
  have allocated : newDestination config.layout environment.act descriptor.ty .value 0 none (some 2) .initial = .ok 0 buildReady := by
    unfold buildReady stepState config environment descriptor implementation
    cbv
  have builtEvents : (Goose.Proofs.Exit.stepState (buildExpr 38 config environment 0 expression buildReady)).construction.events =
      [.begin 0, .write 0 0, .write 0 1] := by
    unfold buildReady stepState config environment expression descriptor implementation
    cbv
  have events : after.construction.events = [.begin 0, .write 0 0, .write 0 1, .publish 0] := by
    unfold after stepState config environment statement expression descriptor implementation
    cbv
  let visit : StatementInvocation := ⟨environment.act, 0, 39, statement, .initial, .ok (.normal .unit) after⟩
  have replay : StatementReplay config environment 40 0 [statement] .initial (.ok (.normal .unit) after) [visit] :=
    .next actual (.done 38 1 after)
  have root : rootOf environment 0 .initial = .ok (.local 4 1 0) .initial := by
    unfold rootOf environment descriptor
    cbv
  have direct : ordinaryProducerCount? 38 ⟨config.module, environment.vars⟩ expression = none := by
    unfold config environment expression descriptor implementation
    cbv
  have allocated' : newDestination config.layout environment.act descriptor.ty .value 0 none
      (producerCount? ⟨config.module, environment.vars⟩ expression) .initial = .ok 0 buildReady := by
    simpa [expression, producerCount?, literalCount] using allocated
  obtain ⟨history, retained⟩ := directDeclaration_visit_sourceEvents replay visit (by simp [visit])
    38 0 expression 0 descriptor (.local 4 1 0) implementation .initial buildReady 0 rfl rfl rfl rfl root rfl rfl direct allocated'
    (.legacy 38 (.builderBytes environment 0 (.varr (.int .u8)) [65, 66] 0))
  exact ⟨after, buildReady, [visit], replay, allocated, ⟨visit, by simp, history, retained⟩, builtEvents, events⟩

#print axioms directInitializer_sourceEvents
end Goose.Proofs.ConstructionGhostDirectDeclarationEventsWitness
