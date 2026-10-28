import Goose.Proofs.ConstructionAcceptedBinaryRegisterCall
import Goose.Proofs.ConstructionAcceptedNestedGlobal

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

private def binaryCallSummary : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def binaryCallEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, binaryCallSummary⟩
private def binaryCallLeaf : Impl := ⟨"leaf", #[], #[⟨.int .i64, .register, none⟩], #[],
  .mk 0 [] (some (.lit .i64 7)), binaryCallSummary⟩
private def binaryCallExpression : Expr := .bin .add (.call 1 [] 0) (.lit .i64 3) 0
private def binaryCallModule : Module := ⟨#["binary-call.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, binaryCallExpression, 0⟩], #[binaryCallEntry, binaryCallLeaf],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "leaf", [], [[]], []⟩], 0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def binaryCallConfig : EvalConfig := ⟨.release, binaryCallModule⟩

theorem binaryCall_validated : validate binaryCallModule = .ok () := by cbv

theorem binaryCall_graph : RegisterCallGraphWithCallLocals binaryCallConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [binaryCallConfig, binaryCallModule] at contextAt
    subst context
    simp [binaryCallConfig, binaryCallModule] at implementationAt
    subst implementation
    simp [binaryCallEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [binaryCallConfig, binaryCallModule] at contextAt
      subst context
      simp [binaryCallConfig, binaryCallModule] at implementationAt
      subst implementation
      apply Or.inl
      refine ⟨_, rfl, Or.inl ⟨0, [], .lit .i64 7, rfl, .nil, ?_, ?_⟩⟩
      · repeat constructor
      · intro id expression origin member
        cases member
    | succ target => simp [binaryCallConfig, binaryCallModule] at contextAt

private def binaryCallObservation : Option Int :=
  match runModule 40 binaryCallConfig .initial with
  | .ok () state => match state.objects.lookup (.global 0) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem binaryCall_result : binaryCallObservation = some 10 := by decide +kernel

theorem binaryCall_evaluation_allFuel (fuel : Nat) :
    ∃ types live ambient,
      let activated := { ExecutionState.initial with nextAct := ExecutionState.initial.nextAct + 1 }
      let environment : RuntimeActivation := ⟨0, ExecutionState.initial.nextAct, #[], [], []⟩
      let outcome := evalValue fuel binaryCallConfig environment binaryCallExpression activated
      AcceptedWorld binaryCallConfig 0 (Goose.Proofs.Exit.stepState outcome) ambient types live [] [] ∧
      FutureGlobalsClear binaryCallConfig 0 (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok value _ => ambient = [] ∧ ValueRepresentation (.int .i64) value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, binaryCallExpression, 0⟩
  obtain ⟨names, roots, typingAfter, rootsAfter, world, source, checked⟩ :=
    accepted_nestedGlobal_checked binaryCallConfig (acceptedModule binaryCallConfig binaryCall_validated) 0 descriptor .initial []
      (declaredRootTypes binaryCallModule) (fun _ => False) (initial_acceptedWorld binaryCallConfig binaryCall_validated)
      (futureGlobalsClear_initial binaryCallConfig) (by rfl) (Or.inl ⟨.i64, rfl⟩)
  let frame := scalarGlobalInitializerFrame binaryCallConfig 0 ExecutionState.initial.nextAct names
  let activated := { ExecutionState.initial with nextAct := ExecutionState.initial.nextAct + 1 }
  have left : UnaryRegisterExpression binaryCallConfig .i64 (.call 1 [] 0) :=
    .call 1 0 ⟨1, "leaf", [], [[]], []⟩ binaryCallLeaf rfl rfl rfl rfl
  have right : UnaryRegisterExpression binaryCallConfig .i64 (.lit .i64 3) :=
    .scalar (.numeric (.scalar (.scalar (.integer .i64 3))))
  obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, result⟩ :=
    evalValue_binary_unaryRegister fuel binaryCallConfig .i64 (acceptedModule binaryCallConfig binaryCall_validated)
      frame activated [] (declaredRootTypes binaryCallModule) (fun _ => False) [] [] .add (.call 1 [] 0) (.lit .i64 3) 0
      left right binaryCall_graph world source roots typingAfter rootsAfter checked
  exact ⟨nextTypes, nextLive, nextAmbient, finalWorld, clear, result⟩

#print axioms binaryCall_evaluation_allFuel
#print axioms binaryCall_result
#print axioms binaryCall_validated
end Goose.Proofs.ConstructionAcceptedExecution
