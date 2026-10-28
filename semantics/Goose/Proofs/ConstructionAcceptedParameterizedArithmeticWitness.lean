import Goose.Proofs.ConstructionAcceptedParameterizedRecursiveGraph
import Goose.Proofs.ConstructionAcceptedRecursiveLocalCallEvaluation
import Goose.Proofs.ConstructionAcceptedSingleScalarGlobal
import Goose.Proofs.ConstructionAcceptedModuleFromGlobals

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

private def parameterArithmeticSummary : Summary := ⟨[], [], [], [], [], [], [], [], true, false⟩
private def parameterArithmeticEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .known parameterArithmeticSummary⟩
private def parameterArithmeticForward : Impl := ⟨"forward", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.call 2 [.byVal (.bin .add (.call 3 [] 0) (.read (.var 0)) 0)] 0)), .known parameterArithmeticSummary⟩
private def parameterArithmeticIdentity : Impl := ⟨"identity", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.bin .add (.read (.var 0)) (.lit .i64 3) 0)), .known parameterArithmeticSummary⟩
private def parameterArithmeticLeaf : Impl := ⟨"leaf", #[], #[⟨.int .i64, .register, none⟩], #[],
  .mk 0 [] (some (.lit .i64 7)), .known parameterArithmeticSummary⟩
private def parameterArithmeticModule : Module := ⟨#["parameter-arithmetic.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩],
  #[parameterArithmeticEntry, parameterArithmeticForward, parameterArithmeticIdentity, parameterArithmeticLeaf],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "forward", [], [[]], []⟩, ⟨2, "identity", [], [[]], []⟩, ⟨3, "leaf", [], [[]], []⟩], 0,
  #[⟨0, 1, "call"⟩], #[], #[]⟩
private def parameterArithmeticConfig : EvalConfig := ⟨.release, parameterArithmeticModule⟩

theorem parameterArithmetic_validated : validate parameterArithmeticModule = .ok () := by cbv

theorem parameterArithmetic_graph : ParameterizedArithmeticRegisterGraph parameterArithmeticConfig .i64 := by
  intro target context implementation parameter contextAt implementationAt parameters mode results
  cases target with
  | zero =>
    simp [parameterArithmeticConfig, parameterArithmeticModule] at contextAt
    subst context
    simp [parameterArithmeticConfig, parameterArithmeticModule] at implementationAt
    subst implementation
    simp [parameterArithmeticEntry] at parameters
  | succ target =>
    cases target with
    | zero =>
      simp [parameterArithmeticConfig, parameterArithmeticModule] at contextAt
      subst context
      simp [parameterArithmeticConfig, parameterArithmeticModule] at implementationAt
      subst implementation
      have same : parameter = ⟨0, .byValue⟩ := by simpa [parameterArithmeticForward] using parameters.symm
      subst parameter
      apply Or.inr
      apply Or.inr
      refine ⟨⟨"value", .int .i64, .immutable, 0, 0⟩, parameterArithmeticSummary, 2, 0,
        ⟨2, "identity", [], [[]], []⟩, parameterArithmeticIdentity, ⟨0, .byValue⟩,
        ⟨"value", .int .i64, .immutable, 0, 0⟩, .bin .add (.call 3 [] 0) (.read (.var 0)) 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | simp [parameterArithmeticSummary] | exact (.binary .add 0 (.operand (.call 3 0 ⟨3, "leaf", [], [[]], []⟩ parameterArithmeticLeaf rfl rfl rfl rfl)) (.operand (.scalar (.numeric (.scalar (.scalar (.localRead 0)))))))
    | succ target =>
      cases target with
      | zero =>
        simp [parameterArithmeticConfig, parameterArithmeticModule] at contextAt
        subst context
        simp [parameterArithmeticConfig, parameterArithmeticModule] at implementationAt
        subst implementation
        apply Or.inr
        apply Or.inl
        refine ⟨⟨"value", .int .i64, .immutable, 0, 0⟩, parameterArithmeticSummary,
          .bin .add (.read (.var 0)) (.lit .i64 3) 0, rfl, rfl, rfl, ?_, rfl, ?_⟩
        · simp [parameterArithmeticSummary]
        · exact .binary .add 0 (.numeric (.scalar (.scalar (.localRead 0))))
            (.numeric (.scalar (.scalar (.integer .i64 3))))
      | succ target =>
        cases target with
        | zero =>
          simp [parameterArithmeticConfig, parameterArithmeticModule] at contextAt
          subst context
          simp [parameterArithmeticConfig, parameterArithmeticModule] at implementationAt
          subst implementation
          simp [parameterArithmeticLeaf] at parameters
        | succ target => simp [parameterArithmeticConfig, parameterArithmeticModule] at contextAt

theorem parameterArithmetic_argumentGraph : RegisterCallGraphWithCallLocals parameterArithmeticConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [parameterArithmeticConfig, parameterArithmeticModule] at contextAt
    subst context
    simp [parameterArithmeticConfig, parameterArithmeticModule] at implementationAt
    subst implementation
    simp [parameterArithmeticEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [parameterArithmeticConfig, parameterArithmeticModule] at contextAt
      subst context
      simp [parameterArithmeticConfig, parameterArithmeticModule] at implementationAt
      subst implementation
      simp [parameterArithmeticForward] at parameters
    | succ target =>
      cases target with
      | zero =>
        simp [parameterArithmeticConfig, parameterArithmeticModule] at contextAt
        subst context
        simp [parameterArithmeticConfig, parameterArithmeticModule] at implementationAt
        subst implementation
        simp [parameterArithmeticIdentity] at parameters
      | succ target =>
        cases target with
        | zero =>
          simp [parameterArithmeticConfig, parameterArithmeticModule] at contextAt
          subst context
          simp [parameterArithmeticConfig, parameterArithmeticModule] at implementationAt
          subst implementation
          apply Or.inl
          refine ⟨_, rfl, Or.inl ⟨0, [], .lit .i64 7, rfl, .nil, ?_, ?_⟩⟩
          · repeat constructor
          · intro id expression origin member
            cases member
        | succ target => simp [parameterArithmeticConfig, parameterArithmeticModule] at contextAt

private def parameterArithmeticObservation : Option Int :=
  match runModule 50 parameterArithmeticConfig .initial with
  | .ok () state => match state.objects.lookup (.global 0) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem parameterArithmetic_result : parameterArithmeticObservation = some 17 := by decide +kernel

theorem parameterArithmetic_module_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld parameterArithmeticConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel parameterArithmeticConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel parameterArithmeticConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let accepted := acceptedModule parameterArithmeticConfig parameterArithmetic_validated
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩
  have initial : InitialGlobalsOutcome fuel parameterArithmeticConfig := by
    apply singleScalarInitialGlobalsOutcome fuel parameterArithmeticConfig accepted descriptor (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
    intro names roots typingAfter rootsAfter frame activated world source checked
    cases fuel with
    | zero =>
      simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨declaredRootTypes parameterArithmeticModule, (fun _ => False), [], (fun _ _ found => found), world, source.futureGlobals, trivial⟩
    | succ fuel =>
      let context : Context := ⟨1, "forward", [], [[]], []⟩
      let parameter : Param := ⟨0, .byValue⟩
      have form : RegisterArithmeticExpression parameterArithmeticConfig .i64 (.lit .i64 7) :=
        .operand (.scalar (.numeric (.scalar (.scalar (.integer .i64 7)))))
      obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, result⟩ :=
        invokeCall_parameterizedArithmeticGraph_allFuel fuel parameterArithmeticConfig .i64 accepted parameterArithmetic_graph parameterArithmetic_argumentGraph
          frame activated [] (declaredRootTypes parameterArithmeticModule) (fun _ => False) [] [] 1 0 context parameterArithmeticForward parameter (.lit .i64 7)
          world source (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) form 4094 (by rfl) roots typingAfter rootsAfter checked
      obtain ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueActs, valueScopes, valueWorld, valueClear, valueResult⟩ :=
        evalValue_registerCall_withArguments_fromInvoke fuel parameterArithmeticConfig 0 frame.interpretation.environment activated []
          (declaredRootTypes parameterArithmeticModule) [] [] 1 context parameterArithmeticForward [.byVal (.lit .i64 7)] (.int .i64) 0
          (by rfl) (by rfl) (by rfl) ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, result⟩
      exact ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueWorld, valueClear, valueResult⟩
  apply acceptedModuleFromGlobals_allFuel fuel parameterArithmeticConfig accepted ⟨0, "entry", [], [], []⟩ parameterArithmeticEntry initial (by rfl) (by rfl)
  · exact .nil
  · simp [parameterArithmeticEntry, Block.stmts]
  · simp [parameterArithmeticEntry, Block.stmts]
  · simp [parameterArithmeticEntry, Block.stmts]
  · simp [parameterArithmeticEntry, Block.stmts]
  · rfl

#print axioms parameterArithmetic_module_allFuel
#print axioms parameterArithmetic_result
#print axioms parameterArithmetic_validated
end Goose.Proofs.ConstructionAcceptedExecution
