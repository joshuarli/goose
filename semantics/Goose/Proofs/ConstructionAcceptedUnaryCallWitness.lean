import Goose.Proofs.ConstructionAcceptedUnaryCallModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

private def unaryCallSummary : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def unaryCallEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, unaryCallSummary⟩
private def unaryCallHelper : Impl := ⟨"helper", #[], #[⟨.int .i64, .register, none⟩], #[],
  .mk 0 [] (some (.lit .i64 7)), unaryCallSummary⟩
private def unaryCallExpression : Expr := .un .neg (.un .neg (.call 1 [] 0) 0) 0
private def unaryCallModule : Module := ⟨#["unary-call.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, unaryCallExpression, 0⟩], #[unaryCallEntry, unaryCallHelper],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [], [[]], []⟩], 0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def unaryCallConfig : EvalConfig := ⟨.release, unaryCallModule⟩

theorem unaryCall_validated : validate unaryCallModule = .ok () := by cbv

theorem unaryCall_form : UnaryRegisterExpression unaryCallConfig .i64 unaryCallExpression := by
  apply UnaryRegisterExpression.unary
  apply UnaryRegisterExpression.unary
  exact .call 1 0 ⟨1, "helper", [], [[]], []⟩ unaryCallHelper rfl rfl rfl rfl

theorem unaryCall_graph : RegisterCallGraphWithCallLocals unaryCallConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [unaryCallConfig, unaryCallModule] at contextAt
    subst context
    simp [unaryCallConfig, unaryCallModule] at implementationAt
    subst implementation
    simp [unaryCallEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [unaryCallConfig, unaryCallModule] at contextAt
      subst context
      simp [unaryCallConfig, unaryCallModule] at implementationAt
      subst implementation
      apply Or.inl
      refine ⟨_, rfl, Or.inl ⟨0, [], .lit .i64 7, rfl, .nil, ?_, ?_⟩⟩
      · repeat constructor
      · intro id expression origin member
        cases member
    | succ target => simp [unaryCallConfig, unaryCallModule] at contextAt

private def unaryCallObservation : Option Int :=
  match runModule 40 unaryCallConfig .initial with
  | .ok () state => match state.objects.lookup (.global 0) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem unaryCall_result : unaryCallObservation = some 7 := by decide +kernel

theorem unaryCall_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld unaryCallConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel unaryCallConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel unaryCallConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, unaryCallExpression, 0⟩
  apply acceptedUnaryCallModule_allFuel fuel unaryCallConfig (acceptedModule unaryCallConfig unaryCall_validated)
    descriptor .i64 (by rfl) (by rfl) (by rfl) unaryCall_form unaryCall_graph ⟨0, "entry", [], [], []⟩ unaryCallEntry (by rfl) (by rfl)
  · exact .nil
  · simp [unaryCallEntry, Block.stmts]
  · simp [unaryCallEntry, Block.stmts]
  · simp [unaryCallEntry, Block.stmts]
  · simp [unaryCallEntry, Block.stmts]
  · rfl

#print axioms unaryCall_allFuel
#print axioms unaryCall_result
#print axioms unaryCall_graph
#print axioms unaryCall_form
#print axioms unaryCall_validated
end Goose.Proofs.ConstructionAcceptedExecution
