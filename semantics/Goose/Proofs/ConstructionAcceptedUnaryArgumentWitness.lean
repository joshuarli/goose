import Goose.Proofs.ConstructionAcceptedUnaryArgumentSource
import Goose.Proofs.ConstructionAcceptedNestedGlobal
import Goose.Proofs.ConstructionAcceptedIdentityUnaryCall
import Goose.Proofs.ConstructionAcceptedSingleScalarGlobal
import Goose.Proofs.ConstructionAcceptedModuleFromGlobals

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

private def unaryArgumentSummary : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def unaryArgumentEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, unaryArgumentSummary⟩
private def unaryArgumentCallee : Impl := ⟨"identity", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.read (.var 0))), unaryArgumentSummary⟩
private def unaryArgumentLeaf : Impl := ⟨"leaf", #[], #[⟨.int .i64, .register, none⟩], #[],
  .mk 0 [] (some (.lit .i64 7)), unaryArgumentSummary⟩
private def unaryArgumentExpression : Expr := .un .neg (.call 2 [] 0) 0
private def unaryArgumentModule : Module := ⟨#["unary-argument.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [.byVal unaryArgumentExpression] 0, 0⟩],
  #[unaryArgumentEntry, unaryArgumentCallee, unaryArgumentLeaf],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "identity", [], [[]], []⟩, ⟨2, "leaf", [], [[]], []⟩],
  0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def unaryArgumentConfig : EvalConfig := ⟨.release, unaryArgumentModule⟩

theorem unaryArgument_validated : validate unaryArgumentModule = .ok () := by cbv

theorem unaryArgument_form : UnaryRegisterExpression unaryArgumentConfig .i64 unaryArgumentExpression := by
  apply UnaryRegisterExpression.unary
  exact .call 2 0 ⟨2, "leaf", [], [[]], []⟩ unaryArgumentLeaf rfl rfl rfl rfl

theorem unaryArgument_graph : RegisterCallGraphWithCallLocals unaryArgumentConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [unaryArgumentConfig, unaryArgumentModule] at contextAt
    subst context
    simp [unaryArgumentConfig, unaryArgumentModule] at implementationAt
    subst implementation
    simp [unaryArgumentEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [unaryArgumentConfig, unaryArgumentModule] at contextAt
      subst context
      simp [unaryArgumentConfig, unaryArgumentModule] at implementationAt
      subst implementation
      simp [unaryArgumentCallee] at parameters
    | succ target =>
      cases target with
      | zero =>
        simp [unaryArgumentConfig, unaryArgumentModule] at contextAt
        subst context
        simp [unaryArgumentConfig, unaryArgumentModule] at implementationAt
        subst implementation
        apply Or.inl
        refine ⟨_, rfl, Or.inl ⟨0, [], .lit .i64 7, rfl, .nil, ?_, ?_⟩⟩
        · repeat constructor
        · intro id expression origin member
          cases member
      | succ target => simp [unaryArgumentConfig, unaryArgumentModule] at contextAt

private def unaryArgumentObservation : Option Int :=
  match runModule 40 unaryArgumentConfig .initial with
  | .ok () state => match state.objects.lookup (.global 0) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem unaryArgument_result : unaryArgumentObservation = some (-7) := by decide +kernel

theorem unaryArgument_allFuel (fuel : Nat) :
    ∃ types live ambient,
      let activated := { ExecutionState.initial with nextAct := ExecutionState.initial.nextAct + 1 }
      let environment : RuntimeActivation := ⟨0, ExecutionState.initial.nextAct, #[], [], []⟩
      let outcome := evalArguments fuel unaryArgumentConfig environment unaryArgumentCallee.vars
        [⟨0, .byValue⟩] [.byVal unaryArgumentExpression] activated
      AcceptedWorld unaryArgumentConfig 0 (Goose.Proofs.Exit.stepState outcome) ambient types live [] [] ∧
      FutureGlobalsClear unaryArgumentConfig 0 (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok values _ => ambient = [] ∧ ∃ value, values = [value] ∧ ValueRepresentation (.int .i64) value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [.byVal unaryArgumentExpression] 0, 0⟩
  obtain ⟨names, roots, typingAfter, rootsAfter, world, source, checked⟩ :=
    accepted_nestedGlobal_checked unaryArgumentConfig (acceptedModule unaryArgumentConfig unaryArgument_validated) 0 descriptor .initial []
      (declaredRootTypes unaryArgumentModule) (fun _ => False) (initial_acceptedWorld unaryArgumentConfig unaryArgument_validated)
      (futureGlobalsClear_initial unaryArgumentConfig) (by rfl) (Or.inl ⟨.i64, rfl⟩)
  let frame := scalarGlobalInitializerFrame unaryArgumentConfig 0 ExecutionState.initial.nextAct names
  let activated := { ExecutionState.initial with nextAct := ExecutionState.initial.nextAct + 1 }
  let context : Context := ⟨1, "identity", [], [[]], []⟩
  let parameter : Param := ⟨0, .byValue⟩
  let localDescriptor : LocalVar := ⟨"value", .int .i64, .immutable, 0, 0⟩
  obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, result⟩ :=
    evalArguments_unaryRegisterExpression_fromChecker frame activated [] (declaredRootTypes unaryArgumentModule) (fun _ => False) [] []
      1 0 context unaryArgumentCallee parameter localDescriptor unaryArgumentExpression .i64 4094 fuel unaryArgument_form unaryArgument_graph
      world source (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (.int .i64) roots typingAfter rootsAfter checked
  exact ⟨nextTypes, nextLive, nextAmbient, finalWorld, clear, result⟩

theorem unaryArgument_module_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld unaryArgumentConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel unaryArgumentConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel unaryArgumentConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let accepted := acceptedModule unaryArgumentConfig unaryArgument_validated
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [.byVal unaryArgumentExpression] 0, 0⟩
  have initial : InitialGlobalsOutcome fuel unaryArgumentConfig := by
    apply singleScalarInitialGlobalsOutcome fuel unaryArgumentConfig accepted descriptor (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
    intro names roots typingAfter rootsAfter frame activated activeWorld frameSource checked
    let context : Context := ⟨1, "identity", [], [[]], []⟩
    let parameter : Param := ⟨0, .byValue⟩
    let localDescriptor : LocalVar := ⟨"value", .int .i64, .immutable, 0, 0⟩
    obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, result⟩ :=
      evalValue_identityUnary_allFuel frame activated [] (declaredRootTypes unaryArgumentModule) (fun _ => False) [] []
        1 0 context unaryArgumentCallee parameter localDescriptor unaryArgumentExpression .i64 4094 fuel unaryArgument_form unaryArgument_graph
        activeWorld frameSource (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (.int .i64) roots typingAfter rootsAfter checked
    exact ⟨nextTypes, nextLive, nextAmbient, extend, finalWorld, clear, result⟩
  apply acceptedModuleFromGlobals_allFuel fuel unaryArgumentConfig accepted
    ⟨0, "entry", [], [], []⟩ unaryArgumentEntry initial (by rfl) (by rfl)
  · exact .nil
  · simp [unaryArgumentEntry, Block.stmts]
  · simp [unaryArgumentEntry, Block.stmts]
  · simp [unaryArgumentEntry, Block.stmts]
  · simp [unaryArgumentEntry, Block.stmts]
  · rfl

#print axioms unaryArgument_module_allFuel
#print axioms unaryArgument_allFuel
#print axioms unaryArgument_result
#print axioms unaryArgument_graph
#print axioms unaryArgument_form
#print axioms unaryArgument_validated
end Goose.Proofs.ConstructionAcceptedExecution
