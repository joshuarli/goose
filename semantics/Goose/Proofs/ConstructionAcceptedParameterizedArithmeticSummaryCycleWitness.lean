import Goose.Proofs.ConstructionAcceptedParameterizedFrameEffects
import Goose.Proofs.ConstructionAcceptedParameterizedRecursiveGraph
import Goose.Proofs.ConstructionAcceptedRecursiveLocalCallEvaluation
import Goose.Proofs.ConstructionAcceptedSingleScalarGlobal
import Goose.Proofs.ConstructionAcceptedModuleFromGlobals
import Goose.Proofs.ConstructionAcceptedNestedGlobal

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

private def parameterArithmeticSummaryCycleSummary : Summary := ⟨[.param 0], [], [], [], [], [], [], [], true, false⟩
private def parameterArithmeticSummaryCycleEntrySummary : Summary := ⟨[], [], [], [], [], [], [], [], true, false⟩
private def parameterArithmeticSummaryCycleEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .known parameterArithmeticSummaryCycleEntrySummary⟩
private def parameterArithmeticSummaryCycleHelper : Impl := ⟨"cycle", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.call 1 [.byVal (.bin .add (.read (.var 0)) (.lit .i64 1) 0)] 0)), .known parameterArithmeticSummaryCycleSummary⟩
private def parameterArithmeticSummaryCycleModule : Module := ⟨#["parameter-arithmetic-summary-cycle.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩], #[parameterArithmeticSummaryCycleEntry, parameterArithmeticSummaryCycleHelper],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "cycle", [], [[]], []⟩], 0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def parameterArithmeticSummaryCycleConfig : EvalConfig := ⟨.release, parameterArithmeticSummaryCycleModule⟩

theorem parameterArithmeticSummaryCycle_validated : validate parameterArithmeticSummaryCycleModule = .ok () := by cbv

private def parameterArithmeticSummaryCycleIsTimeout : Bool :=
  match runModule 40 parameterArithmeticSummaryCycleConfig .initial with
  | .stop .timeout _ => true
  | _ => false

theorem parameterArithmeticSummaryCycle_actual_timeout : parameterArithmeticSummaryCycleIsTimeout = true := by decide +kernel

theorem parameterArithmeticSummaryCycle_graph : ParameterizedScalarSummaryRegisterGraph parameterArithmeticSummaryCycleConfig .i64 := by
  intro target context implementation parameter contextAt implementationAt parameters mode results
  cases target with
  | zero =>
    simp [parameterArithmeticSummaryCycleConfig, parameterArithmeticSummaryCycleModule] at contextAt
    subst context
    simp [parameterArithmeticSummaryCycleConfig, parameterArithmeticSummaryCycleModule] at implementationAt
    subst implementation
    simp [parameterArithmeticSummaryCycleEntry] at parameters
  | succ target =>
    cases target with
    | zero =>
      simp [parameterArithmeticSummaryCycleConfig, parameterArithmeticSummaryCycleModule] at contextAt
      subst context
      simp [parameterArithmeticSummaryCycleConfig, parameterArithmeticSummaryCycleModule] at implementationAt
      subst implementation
      have same : parameter = ⟨0, .byValue⟩ := by simpa [parameterArithmeticSummaryCycleHelper] using parameters.symm
      subst parameter
      apply Or.inr
      apply Or.inr
      refine ⟨⟨"value", .int .i64, .immutable, 0, 0⟩, parameterArithmeticSummaryCycleSummary, 1, 0,
        ⟨1, "cycle", [], [[]], []⟩, parameterArithmeticSummaryCycleHelper, ⟨0, .byValue⟩,
        ⟨"value", .int .i64, .immutable, 0, 0⟩, .bin .add (.read (.var 0)) (.lit .i64 1) 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | exact Or.inr ⟨Or.inr ⟨.add, .read (.var 0), .lit .i64 1, 0, rfl, .binary .add 0 (.numeric (.scalar (.scalar (.localRead 0)))) (.numeric (.scalar (.scalar (.integer .i64 1))))⟩, parameterArithmeticSummaryCycleSummary, rfl⟩ | exact .operand (.scalar (.binary .add 0 (.numeric (.scalar (.scalar (.localRead 0)))) (.numeric (.scalar (.scalar (.integer .i64 1))))))
    | succ target => simp [parameterArithmeticSummaryCycleConfig, parameterArithmeticSummaryCycleModule] at contextAt

theorem parameterArithmeticSummaryCycle_argumentGraph : RegisterCallGraphWithCallLocals parameterArithmeticSummaryCycleConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [parameterArithmeticSummaryCycleConfig, parameterArithmeticSummaryCycleModule] at contextAt
    subst context
    simp [parameterArithmeticSummaryCycleConfig, parameterArithmeticSummaryCycleModule] at implementationAt
    subst implementation
    simp [parameterArithmeticSummaryCycleEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [parameterArithmeticSummaryCycleConfig, parameterArithmeticSummaryCycleModule] at contextAt
      subst context
      simp [parameterArithmeticSummaryCycleConfig, parameterArithmeticSummaryCycleModule] at implementationAt
      subst implementation
      simp [parameterArithmeticSummaryCycleHelper] at parameters
    | succ target => simp [parameterArithmeticSummaryCycleConfig, parameterArithmeticSummaryCycleModule] at contextAt

theorem parameterArithmeticSummaryCycle_module_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld parameterArithmeticSummaryCycleConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel parameterArithmeticSummaryCycleConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel parameterArithmeticSummaryCycleConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let accepted := acceptedModule parameterArithmeticSummaryCycleConfig parameterArithmeticSummaryCycle_validated
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩
  have initial : InitialGlobalsOutcome fuel parameterArithmeticSummaryCycleConfig := by
    apply singleScalarInitialGlobalsOutcome fuel parameterArithmeticSummaryCycleConfig accepted descriptor (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
    intro names roots typingAfter rootsAfter frame activated world source checked
    cases fuel with
    | zero =>
      simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨declaredRootTypes parameterArithmeticSummaryCycleModule, (fun _ => False), [], (fun _ _ found => found), world, source.futureGlobals, trivial⟩
    | succ fuel =>
      let context : Context := ⟨1, "cycle", [], [[]], []⟩
      let parameter : Param := ⟨0, .byValue⟩
      have form : UnaryRegisterExpression parameterArithmeticSummaryCycleConfig .i64 (.lit .i64 7) :=
        .scalar (.numeric (.scalar (.scalar (.integer .i64 7))))
      obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, result⟩ :=
        invokeCall_parameterizedScalarSummaryGraph_allFuel fuel parameterArithmeticSummaryCycleConfig .i64 accepted parameterArithmeticSummaryCycle_graph parameterArithmeticSummaryCycle_argumentGraph
          frame activated [] (declaredRootTypes parameterArithmeticSummaryCycleModule) (fun _ => False) [] [] 1 0 context parameterArithmeticSummaryCycleHelper parameter (.lit .i64 7)
          world source (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (.operand form) 4094 (by rfl) roots typingAfter rootsAfter checked
      obtain ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueActs, valueScopes, valueWorld, valueClear, valueResult⟩ :=
        evalValue_registerCall_withArguments_fromInvoke fuel parameterArithmeticSummaryCycleConfig 0 frame.interpretation.environment activated []
          (declaredRootTypes parameterArithmeticSummaryCycleModule) [] [] 1 context parameterArithmeticSummaryCycleHelper [.byVal (.lit .i64 7)] (.int .i64) 0
          (by rfl) (by rfl) (by rfl) ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, result⟩
      exact ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueWorld, valueClear, valueResult⟩
  apply acceptedModuleFromGlobals_allFuel fuel parameterArithmeticSummaryCycleConfig accepted ⟨0, "entry", [], [], []⟩ parameterArithmeticSummaryCycleEntry initial (by rfl) (by rfl)
  · exact .nil
  · simp [parameterArithmeticSummaryCycleEntry, Block.stmts]
  · simp [parameterArithmeticSummaryCycleEntry, Block.stmts]
  · simp [parameterArithmeticSummaryCycleEntry, Block.stmts]
  · simp [parameterArithmeticSummaryCycleEntry, Block.stmts]
  · rfl

#print axioms parameterArithmeticSummaryCycle_module_allFuel
#print axioms parameterArithmeticSummaryCycle_argumentGraph
#print axioms parameterArithmeticSummaryCycle_graph
#print axioms parameterArithmeticSummaryCycle_actual_timeout
#print axioms parameterArithmeticSummaryCycle_validated
end Goose.Proofs.ConstructionAcceptedExecution
