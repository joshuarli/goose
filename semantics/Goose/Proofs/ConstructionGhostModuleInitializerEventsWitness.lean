import Goose.Proofs.ConstructionGhostModuleInitializerEvents

namespace Goose.Proofs.ConstructionGhostModuleInitializerEventsWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostStatementEvents
open Goose.Proofs.ConstructionGhostInvocationEventChunks Goose.Proofs.ConstructionGhostMaterializedDeclarationEvents
open Goose.Proofs.ConstructionGhostModuleInitializerEvents

private def context : Context := ⟨0, "entry", [], [], []⟩
private def bytes : Expr := .bytes (.varr (.int .u8)) [65, 66] 0
private def element : Expr := .len (.val bytes)
private def materialized : Expr := .values [.arrLit (.arr (.int .i64) 1) [element] 0]
private def fixedVar : LocalVar := ⟨"fixed", .int .i64, .immutable, 0, 0⟩
private def dynamicVar : LocalVar := ⟨"dynamic", .varr (.int .i64), .immutable, 0, 0⟩
private def statements : List Stmt := [.letS 0 element 0, .letS 1 materialized 0]
private def implementation : Impl := ⟨"entry", #[], #[], #[fixedVar, dynamicVar], .mk 0 statements none, .unknown⟩
private def config : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def activation : RuntimeActivation := ⟨0, 0, #[fixedVar, dynamicVar], [], []⟩
private def activated : ExecutionState := { ExecutionState.initial with nextAct := 1, activations := [activation] }
private def scopedEnvironment : RuntimeActivation := { activation with scopes := [(0, 0)] }
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem supported : ∀ sourceFuel id expr origin, .letS id expr origin ∈ statements →
    FuelSupport config sourceFuel (.value scopedEnvironment expr) := by
  intro sourceFuel id expr origin member
  simp only [statements, List.mem_cons, List.not_mem_nil, or_false] at member
  have elementSupport : SupportedOperation config (.value scopedEnvironment element) :=
    .lengthValue _ (.val bytes) (.valueView _ bytes (.valueBytes _ (.varr (.int .u8)) [65, 66] 0))
  rcases member with same | same
  · cases same
    exact .legacy sourceFuel elementSupport
  · cases same
    apply FuelSupport.legacy
    apply SupportedOperation.singleton scopedEnvironment (.arrLit (.arr (.int .i64) 1) [element] 0)
    apply SupportedOperation.aggregate scopedEnvironment (.arrLit (.arr (.int .i64) 1) [element] 0) [element]
      (.fixedArray (.arr (.int .i64) 1) [element] 0 rfl)
    intro operand inOperands
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inOperands
    subst operand
    exact elementSupport

theorem module_mixedInitializerEvents : ∃ outcome visits chunks final,
    StatementReplay config scopedEnvironment 47 0 statements
      (Goose.Proofs.ConstructionGhostResultScope.resultScopeStart activation 0 activated) outcome visits ∧
    visits.map StatementInvocation.statement = statements.take visits.length ∧
    (visits.map StatementInvocation.ordinal).Nodup ∧ ChunksAlign (visits.map statementInvocation) chunks ∧
    FixedVisitSourceEvents config scopedEnvironment visits ∧ MaterializedVisitSourceEvents config scopedEnvironment visits ∧
    chunks.flatten ≠ [] ∧ runModule 50 config .initial = .ok () final ∧ final.construction.events ≠ [] := by
  obtain ⟨outcome, visits, chunks, replay, ordered, once, aligned, finalEq, fixed, materializedEvents, moduleExecution⟩ :=
    runModule_entryInitializerEvents 47 config context implementation rfl rfl rfl rfl rfl 0 statements none rfl supported
  refine ⟨outcome, visits, chunks, stepState (runModule 50 config .initial), replay, ordered, once, aligned, fixed, materializedEvents, ?_, ?_, ?_⟩
  · have prefixEq : (Goose.Proofs.Exit.stepState outcome).construction.events = chunks.flatten := by
      simpa [Goose.Proofs.ConstructionGhostResultScope.resultScopeStart, activation, activated, ExecutionState.initial, ConstructionState.initial] using finalEq
    rw [← prefixEq, ← replay.sound]
    intro empty
    unfold config context implementation fixedVar dynamicVar statements materialized element bytes at empty
    cbv at empty
    all_goals try (unfold evalValue at empty; cbv at empty)
    all_goals try (unfold evalValue at empty; cbv at empty)
    all_goals try (unfold evalValue at empty; cbv at empty)
    all_goals cases empty
  · unfold stepState config context implementation fixedVar dynamicVar statements materialized element bytes
    cbv
    all_goals try (unfold evalValue; cbv)
    all_goals try (unfold evalValue; cbv)
    all_goals try (unfold evalValue; cbv)
  · intro empty
    unfold stepState config context implementation fixedVar dynamicVar statements materialized element bytes at empty
    cbv at empty
    all_goals try (unfold evalValue at empty; cbv at empty)
    all_goals try (unfold evalValue at empty; cbv at empty)
    all_goals try (unfold evalValue at empty; cbv at empty)
    all_goals cases empty

#print axioms module_mixedInitializerEvents
end Goose.Proofs.ConstructionGhostModuleInitializerEventsWitness
