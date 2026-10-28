import Goose.Proofs.ConstructionAcceptedIdentityUnaryCall
import Goose.Proofs.ConstructionAcceptedNestedGlobal

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

private def scalarArgumentSummary : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def scalarArgumentEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, scalarArgumentSummary⟩
private def scalarArgumentCallee : Impl := ⟨"identity", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.read (.var 0))), scalarArgumentSummary⟩
private def scalarArgumentExpression : Expr := .bin .add (.lit .i64 2) (.lit .i64 3) 0
private def scalarArgumentModule : Module := ⟨#["scalar-argument.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [.byVal scalarArgumentExpression] 0, 0⟩],
  #[scalarArgumentEntry, scalarArgumentCallee], #[⟨0, "entry", [], [], []⟩, ⟨1, "identity", [], [[]], []⟩],
  0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def scalarArgumentConfig : EvalConfig := ⟨.release, scalarArgumentModule⟩

theorem scalarArgument_validated : validate scalarArgumentModule = .ok () := by cbv

theorem scalarArgument_form : UnaryRegisterExpression scalarArgumentConfig .i64 scalarArgumentExpression := by
  apply UnaryRegisterExpression.scalar
  exact .binary .add 0 (.numeric (.scalar (.scalar (.integer .i64 2))))
    (.numeric (.scalar (.scalar (.integer .i64 3))))

theorem scalarArgument_graph : RegisterCallGraphWithCallLocals scalarArgumentConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [scalarArgumentConfig, scalarArgumentModule] at contextAt
    subst context
    simp [scalarArgumentConfig, scalarArgumentModule] at implementationAt
    subst implementation
    simp [scalarArgumentEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [scalarArgumentConfig, scalarArgumentModule] at contextAt
      subst context
      simp [scalarArgumentConfig, scalarArgumentModule] at implementationAt
      subst implementation
      simp [scalarArgumentCallee] at parameters
    | succ target => simp [scalarArgumentConfig, scalarArgumentModule] at contextAt

private def scalarArgumentObservation : Option Int :=
  match runModule 40 scalarArgumentConfig .initial with
  | .ok () state => match state.objects.lookup (.global 0) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem scalarArgument_result : scalarArgumentObservation = some 5 := by decide +kernel

theorem scalarArgument_invoke_allFuel (fuel : Nat) :
    ∃ types live ambient,
      let activated := { ExecutionState.initial with nextAct := ExecutionState.initial.nextAct + 1 }
      let environment : RuntimeActivation := ⟨0, ExecutionState.initial.nextAct, #[], [], []⟩
      let outcome := invokeCall fuel scalarArgumentConfig environment 1 [.byVal scalarArgumentExpression] [.register (.int .i64)] 0 activated
      AcceptedWorld scalarArgumentConfig 0 (Goose.Proofs.Exit.stepState outcome) ambient types live [] [] ∧
      FutureGlobalsClear scalarArgumentConfig 0 (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok carriers _ => ambient = [] ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation (.int .i64) value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [.byVal scalarArgumentExpression] 0, 0⟩
  obtain ⟨names, roots, typingAfter, rootsAfter, world, source, checked⟩ :=
    accepted_nestedGlobal_checked scalarArgumentConfig (acceptedModule scalarArgumentConfig scalarArgument_validated) 0 descriptor .initial []
      (declaredRootTypes scalarArgumentModule) (fun _ => False) (initial_acceptedWorld scalarArgumentConfig scalarArgument_validated)
      (futureGlobalsClear_initial scalarArgumentConfig) (by rfl) (Or.inl ⟨.i64, rfl⟩)
  let frame := scalarGlobalInitializerFrame scalarArgumentConfig 0 ExecutionState.initial.nextAct names
  let activated := { ExecutionState.initial with nextAct := ExecutionState.initial.nextAct + 1 }
  let context : Context := ⟨1, "identity", [], [[]], []⟩
  let parameter : Param := ⟨0, .byValue⟩
  let localDescriptor : LocalVar := ⟨"value", .int .i64, .immutable, 0, 0⟩
  obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, result⟩ :=
    invokeCall_identityUnary_allFuel frame activated [] (declaredRootTypes scalarArgumentModule) (fun _ => False) [] []
      1 0 context scalarArgumentCallee parameter localDescriptor scalarArgumentExpression .i64 4094 fuel scalarArgument_form scalarArgument_graph
      world source (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (.int .i64) roots typingAfter rootsAfter checked
  exact ⟨nextTypes, nextLive, nextAmbient, finalWorld, clear, result⟩

#print axioms scalarArgument_invoke_allFuel
#print axioms scalarArgument_result
#print axioms scalarArgument_validated
end Goose.Proofs.ConstructionAcceptedExecution
