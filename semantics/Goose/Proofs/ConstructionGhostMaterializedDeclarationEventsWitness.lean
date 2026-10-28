import Goose.Proofs.ConstructionGhostMaterializedDeclarationEvents

namespace Goose.Proofs.ConstructionGhostMaterializedDeclarationEventsWitness
open Goose.Construct Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostSourceFuel Goose.Proofs.ConstructionGhostMaterializedDeclarationEvents

private def bytes : Expr := .bytes (.varr (.int .u8)) [65, 66] 0
private def element : Expr := .len (.val bytes)
private def expression : Expr := .values [.arrLit (.arr (.int .i64) 1) [element] 0]
private def descriptor : LocalVar := ⟨"x", .varr (.int .i64), .immutable, 0, 0⟩
private def statement : Stmt := .letS 0 expression 0
private def implementation : Impl := ⟨"entry", #[], #[], #[descriptor], .mk 0 [] none, .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 4, #[descriptor], [(0, 1)], []⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem supported : FuelSupport config 38 (.value environment expression) := by
  apply FuelSupport.legacy
  apply SupportedOperation.singleton environment (.arrLit (.arr (.int .i64) 1) [element] 0)
  apply SupportedOperation.aggregate environment (.arrLit (.arr (.int .i64) 1) [element] 0) [element]
    (.fixedArray (.arr (.int .i64) 1) [element] 0 rfl)
  intro operand member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst operand
  exact .lengthValue environment (.val bytes) (.valueView environment bytes (.valueBytes environment (.varr (.int .u8)) [65, 66] 0))

theorem materializedInitializer_sourceEvents : ∃ after visits,
    StatementReplay config environment 40 0 [statement] .initial (.ok (.normal .unit) after) visits ∧
    (∃ visit ∈ visits,
      SourceHistory config 38 [environment.act, visit.ordinal, 0] (.value environment expression) .initial
        (evalValue 38 config environment expression .initial) ∧
      Goose.Proofs.ConstructionExecution.EventPrefix
        (Goose.Proofs.Exit.stepState (evalValue 38 config environment expression .initial)).construction.events
        (Goose.Proofs.Exit.stepState visit.outcome).construction.events) ∧
    (Goose.Proofs.Exit.stepState (evalValue 38 config environment expression .initial)).construction.events =
      [.begin 0, .write 0 0, .write 0 1, .publish 0] := by
  let after := stepState (execStmt 39 config environment statement .initial)
  have actual : execStmt 39 config environment statement .initial = .ok (.normal .unit) after := by
    unfold after stepState config environment statement expression element bytes descriptor implementation
    unfold execStmt
    unfold evalValue
    cbv
    unfold evalValue
    cbv
  have sourceEvents : (Goose.Proofs.Exit.stepState (evalValue 38 config environment expression .initial)).construction.events =
      [.begin 0, .write 0 0, .write 0 1, .publish 0] := by
    unfold config environment expression element bytes descriptor implementation
    unfold evalValue
    cbv
    unfold evalValue
    cbv
  let visit : StatementInvocation := ⟨environment.act, 0, 39, statement, .initial, .ok (.normal .unit) after⟩
  have replay : StatementReplay config environment 40 0 [statement] .initial (.ok (.normal .unit) after) [visit] :=
    .next actual (.done 38 1 after)
  have root : rootOf environment 0 .initial = .ok (.local 4 1 0) .initial := by
    unfold rootOf environment descriptor
    cbv
  have count : ordinaryProducerCount? 38 ⟨config.module, environment.vars⟩ expression = some 1 := by
    unfold config environment expression element bytes descriptor implementation
    cbv
  obtain ⟨history, initial, retained⟩ := materializedDeclaration_visit_sourceEvents replay visit (by simp [visit])
    38 0 expression 0 descriptor (.local 4 1 0) implementation 1 .initial rfl rfl rfl rfl root rfl rfl count supported
  exact ⟨after, [visit], replay, ⟨visit, by simp, history, retained⟩, sourceEvents⟩

#print axioms materializedInitializer_sourceEvents
end Goose.Proofs.ConstructionGhostMaterializedDeclarationEventsWitness
