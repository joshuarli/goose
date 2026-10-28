import Goose.Proofs.ConstructionGhostFixedDeclarationEvents

namespace Goose.Proofs.ConstructionGhostFixedDeclarationEventsWitness
open Goose.Construct Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostDeclaration
open Goose.Proofs.ConstructionGhostFixedDeclarationEvents Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostSyntaxFuel

private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 4, #[⟨"x", .int .i64, .immutable, 0, 0⟩], [(0, 1)], []⟩
private def expression : Expr := .len (.val (.bytes (.varr (.int .u8)) [65, 66] 0))
private def statement : Stmt := .letS 0 expression 0
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem closed : ClosedModuleWithTails config := by
  intro contextId actualContext actualImplementation found implFound
  simp [config] at found

private theorem expressionSyntax : ValueSyntax config expression :=
  .length (.val (.bytes (.varr (.int .u8)) [65, 66] 0))
    (.value _ (.bytes (.varr (.int .u8)) [65, 66] 0))

theorem fixedInitializer_sourceEvents : ∃ after visits,
    StatementReplay config environment 40 0 [statement] .initial (.ok (.normal .unit) after) visits ∧
    (∃ visit ∈ visits,
      SourceHistory config 38 [environment.act, visit.ordinal, 0] (.value environment expression) .initial
        (evalValue 38 config environment expression .initial) ∧
      (Goose.Proofs.Exit.stepState visit.outcome).construction.events =
        (Goose.Proofs.Exit.stepState (evalValue 38 config environment expression .initial)).construction.events) ∧
    after.construction.events = [.begin 0, .write 0 0, .write 0 1, .publish 0] := by
  let after := stepState (execStmt 39 config environment statement .initial)
  have actual : execStmt 39 config environment statement .initial = .ok (.normal .unit) after := by
    unfold after stepState config environment statement expression
    unfold execStmt
    unfold evalValue
    cbv
    unfold evalValue
    cbv
  have events : after.construction.events = [.begin 0, .write 0 0, .write 0 1, .publish 0] := by
    unfold after stepState config environment statement expression
    unfold execStmt
    unfold evalValue
    cbv
    unfold evalValue
    cbv
  let visit : StatementInvocation := ⟨environment.act, 0, 39, statement, .initial, .ok (.normal .unit) after⟩
  have replay : StatementReplay config environment 40 0 [statement] .initial (.ok (.normal .unit) after) [visit] :=
    .next actual (.done 38 1 after)
  have root : rootOf environment 0 .initial = .ok (.local 4 1 0) .initial := by
    unfold rootOf environment
    cbv
  obtain ⟨history, beforeEvents, sourceEvents, retained⟩ := fixedDeclaration_visit_syntaxEvents replay closed visit (by simp [visit])
    38 0 expression 0 ⟨"x", .int .i64, .immutable, 0, 0⟩ (.local 4 1 0) .initial rfl rfl rfl rfl root expressionSyntax
  exact ⟨after, [visit], replay, ⟨visit, by simp, history, sourceEvents⟩, events⟩

#print axioms fixedInitializer_sourceEvents
end Goose.Proofs.ConstructionGhostFixedDeclarationEventsWitness
