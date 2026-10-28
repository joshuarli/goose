import Goose.Proofs.ConstructionAcceptedIdentityArithmeticCall
import Goose.Proofs.ConstructionAcceptedSingleScalarGlobal
import Goose.Proofs.ConstructionAcceptedModuleFromGlobals

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

private def arithmeticArgumentSummary : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def arithmeticArgumentEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, arithmeticArgumentSummary⟩
private def arithmeticArgumentCallee : Impl := ⟨"identity", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.read (.var 0))), arithmeticArgumentSummary⟩
private def arithmeticArgumentLeaf : Impl := ⟨"leaf", #[], #[⟨.int .i64, .register, none⟩], #[],
  .mk 0 [] (some (.lit .i64 7)), arithmeticArgumentSummary⟩
private def arithmeticArgumentExpression : Expr := .bin .mul (.bin .add (.call 2 [] 0) (.lit .i64 3) 0) (.lit .i64 2) 0
private def arithmeticArgumentModule : Module := ⟨#["arithmetic-argument.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [.byVal arithmeticArgumentExpression] 0, 0⟩],
  #[arithmeticArgumentEntry, arithmeticArgumentCallee, arithmeticArgumentLeaf],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "identity", [], [[]], []⟩, ⟨2, "leaf", [], [[]], []⟩],
  0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def arithmeticArgumentConfig : EvalConfig := ⟨.release, arithmeticArgumentModule⟩

theorem arithmeticArgument_validated : validate arithmeticArgumentModule = .ok () := by cbv

theorem arithmeticArgument_form : RegisterArithmeticExpression arithmeticArgumentConfig .i64 arithmeticArgumentExpression := by
  have call : RegisterArithmeticExpression arithmeticArgumentConfig .i64 (.call 2 [] 0) :=
    .operand (.call 2 0 ⟨2, "leaf", [], [[]], []⟩ arithmeticArgumentLeaf rfl rfl rfl rfl)
  have three : RegisterArithmeticExpression arithmeticArgumentConfig .i64 (.lit .i64 3) :=
    .operand (.scalar (.numeric (.scalar (.scalar (.integer .i64 3)))))
  have two : RegisterArithmeticExpression arithmeticArgumentConfig .i64 (.lit .i64 2) :=
    .operand (.scalar (.numeric (.scalar (.scalar (.integer .i64 2)))))
  exact .binary .mul 0 (.binary .add 0 call three) two

theorem arithmeticArgument_graph : RegisterCallGraphWithCallLocals arithmeticArgumentConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [arithmeticArgumentConfig, arithmeticArgumentModule] at contextAt
    subst context
    simp [arithmeticArgumentConfig, arithmeticArgumentModule] at implementationAt
    subst implementation
    simp [arithmeticArgumentEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [arithmeticArgumentConfig, arithmeticArgumentModule] at contextAt
      subst context
      simp [arithmeticArgumentConfig, arithmeticArgumentModule] at implementationAt
      subst implementation
      simp [arithmeticArgumentCallee] at parameters
    | succ target =>
      cases target with
      | zero =>
        simp [arithmeticArgumentConfig, arithmeticArgumentModule] at contextAt
        subst context
        simp [arithmeticArgumentConfig, arithmeticArgumentModule] at implementationAt
        subst implementation
        apply Or.inl
        refine ⟨_, rfl, Or.inl ⟨0, [], .lit .i64 7, rfl, .nil, ?_, ?_⟩⟩
        · repeat constructor
        · intro id expression origin member
          cases member
      | succ target => simp [arithmeticArgumentConfig, arithmeticArgumentModule] at contextAt

private def arithmeticArgumentObservation : Option Int :=
  match runModule 50 arithmeticArgumentConfig .initial with
  | .ok () state => match state.objects.lookup (.global 0) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem arithmeticArgument_result : arithmeticArgumentObservation = some 20 := by decide +kernel

theorem arithmeticArgument_module_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld arithmeticArgumentConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel arithmeticArgumentConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel arithmeticArgumentConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let accepted := acceptedModule arithmeticArgumentConfig arithmeticArgument_validated
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [.byVal arithmeticArgumentExpression] 0, 0⟩
  have initial : InitialGlobalsOutcome fuel arithmeticArgumentConfig := by
    apply singleScalarInitialGlobalsOutcome fuel arithmeticArgumentConfig accepted descriptor (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
    intro names roots typingAfter rootsAfter frame activated world source checked
    let context : Context := ⟨1, "identity", [], [[]], []⟩
    let parameter : Param := ⟨0, .byValue⟩
    let localDescriptor : LocalVar := ⟨"value", .int .i64, .immutable, 0, 0⟩
    obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, result⟩ :=
      evalValue_identityArithmetic_allFuel frame activated [] (declaredRootTypes arithmeticArgumentModule) (fun _ => False) [] []
        1 0 context arithmeticArgumentCallee parameter localDescriptor arithmeticArgumentExpression .i64 4094 fuel arithmeticArgument_form arithmeticArgument_graph
        world source (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (.int .i64) roots typingAfter rootsAfter checked
    exact ⟨nextTypes, nextLive, nextAmbient, extend, finalWorld, clear, result⟩
  apply acceptedModuleFromGlobals_allFuel fuel arithmeticArgumentConfig accepted ⟨0, "entry", [], [], []⟩ arithmeticArgumentEntry initial (by rfl) (by rfl)
  · exact .nil
  · simp [arithmeticArgumentEntry, Block.stmts]
  · simp [arithmeticArgumentEntry, Block.stmts]
  · simp [arithmeticArgumentEntry, Block.stmts]
  · simp [arithmeticArgumentEntry, Block.stmts]
  · rfl

#print axioms arithmeticArgument_module_allFuel
#print axioms arithmeticArgument_result
#print axioms arithmeticArgument_validated
end Goose.Proofs.ConstructionAcceptedExecution
