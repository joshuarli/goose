import Goose.Proofs.ConstructionGhostModuleActivationEvents

namespace Goose.Proofs.ConstructionGhostModuleActivationEventsWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostStatementEvents
open Goose.Proofs.ConstructionGhostInvocationEventChunks Goose.Proofs.ConstructionGhostModuleActivationEvents

private def context : Context := ⟨0, "entry", [], [], []⟩
private def expression : Expr := .len (.val (.bytes (.varr (.int .u8)) [65, 66] 0))
private def localVar : LocalVar := ⟨"x", .int .i64, .immutable, 0, 0⟩
private def statement : Stmt := .letS 0 expression 0
private def implementation : Impl := ⟨"entry", #[], #[], #[localVar], .mk 0 [statement] none, .unknown⟩
private def config : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def activation : RuntimeActivation := ⟨0, 0, #[localVar], [], []⟩
private def activated : ExecutionState := { ExecutionState.initial with nextAct := 1, activations := [activation] }
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem supported : ∀ sourceFuel id expr origin, .letS id expr origin ∈ [statement] →
    FuelSupport config sourceFuel (.value ⟨0, 0, implementation.vars, [(0, 0)], []⟩ expr) := by
  intro sourceFuel id expr origin member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  have same : Stmt.letS id expr origin = Stmt.letS 0 expression 0 := member
  cases same
  exact .legacy sourceFuel (.lengthValue _ (.val (.bytes (.varr (.int .u8)) [65, 66] 0))
    (.valueView _ _ (.valueBytes _ (.varr (.int .u8)) [65, 66] 0)))

theorem module_fixedInitializerEvents : ∃ outcome visits chunks final,
    StatementReplay config { activation with scopes := [(0, 0)] } 37 0 [statement]
      (Goose.Proofs.ConstructionGhostResultScope.resultScopeStart activation 0 activated) outcome visits ∧
    visits.map StatementInvocation.statement = [statement].take visits.length ∧
    (visits.map StatementInvocation.ordinal).Nodup ∧ ChunksAlign (visits.map statementInvocation) chunks ∧
    chunks.flatten = [.begin 0, .write 0 0, .write 0 1, .publish 0] ∧
    runModule 40 config .initial = .ok () final ∧
    final.construction.events = [.begin 0, .write 0 0, .write 0 1, .publish 0] := by
  obtain ⟨outcome, visits, chunks, replay, ordered, once, aligned, finalEq, moduleExecution, enterExecution, bodyExecution, sources⟩ :=
    runModule_fixedEntryEvents 37 config context implementation rfl rfl rfl rfl rfl 0 [statement] none rfl supported
  refine ⟨outcome, visits, chunks, stepState (runModule 40 config .initial), replay, ordered, once, aligned, ?_, ?_, ?_⟩
  · have prefixEq : (Goose.Proofs.Exit.stepState outcome).construction.events = chunks.flatten := by
      simpa [Goose.Proofs.ConstructionGhostResultScope.resultScopeStart, activation, activated, ExecutionState.initial, ConstructionState.initial] using finalEq
    rw [← prefixEq, ← replay.sound]
    unfold config context implementation localVar statement expression
    cbv
    unfold evalValue
    cbv
  · unfold stepState config context implementation localVar statement expression
    cbv
    unfold evalValue
    cbv
  · unfold stepState config context implementation localVar statement expression
    cbv
    unfold evalValue
    cbv

#print axioms module_fixedInitializerEvents
end Goose.Proofs.ConstructionGhostModuleActivationEventsWitness
