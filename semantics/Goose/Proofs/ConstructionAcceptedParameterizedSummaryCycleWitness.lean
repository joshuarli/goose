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

private def parameterSummaryCycleSummary : Summary := ⟨[.param 0], [], [], [], [], [], [], [], false, false⟩
private def parameterSummaryCycleEntrySummary : Summary := ⟨[], [], [], [], [], [], [], [], false, false⟩
private def parameterSummaryCycleEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .known parameterSummaryCycleEntrySummary⟩
private def parameterSummaryCycleHelper : Impl := ⟨"cycle", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.call 1 [.byVal (.read (.var 0))] 0)), .known parameterSummaryCycleSummary⟩
private def parameterSummaryCycleModule : Module := ⟨#["parameter-summary-cycle.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩], #[parameterSummaryCycleEntry, parameterSummaryCycleHelper],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "cycle", [], [[]], []⟩], 0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def parameterSummaryCycleConfig : EvalConfig := ⟨.release, parameterSummaryCycleModule⟩

theorem parameterSummaryCycle_validated : validate parameterSummaryCycleModule = .ok () := by cbv

private def parameterSummaryCycleIsTimeout : Bool :=
  match runModule 40 parameterSummaryCycleConfig .initial with
  | .stop .timeout _ => true
  | _ => false

theorem parameterSummaryCycle_actual_timeout : parameterSummaryCycleIsTimeout = true := by decide +kernel

theorem parameterSummaryCycle_graph : ParameterizedLocalSummaryRegisterGraph parameterSummaryCycleConfig .i64 := by
  intro target context implementation parameter contextAt implementationAt parameters mode results
  cases target with
  | zero =>
    simp [parameterSummaryCycleConfig, parameterSummaryCycleModule] at contextAt
    subst context
    simp [parameterSummaryCycleConfig, parameterSummaryCycleModule] at implementationAt
    subst implementation
    simp [parameterSummaryCycleEntry] at parameters
  | succ target =>
    cases target with
    | zero =>
      simp [parameterSummaryCycleConfig, parameterSummaryCycleModule] at contextAt
      subst context
      simp [parameterSummaryCycleConfig, parameterSummaryCycleModule] at implementationAt
      subst implementation
      have same : parameter = ⟨0, .byValue⟩ := by simpa [parameterSummaryCycleHelper] using parameters.symm
      subst parameter
      apply Or.inr
      apply Or.inr
      refine ⟨⟨"value", .int .i64, .immutable, 0, 0⟩, parameterSummaryCycleSummary, 1, 0,
        ⟨1, "cycle", [], [[]], []⟩, parameterSummaryCycleHelper, ⟨0, .byValue⟩,
        ⟨"value", .int .i64, .immutable, 0, 0⟩, .read (.var 0), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | exact Or.inr ⟨rfl, parameterSummaryCycleSummary, rfl⟩ | exact .operand (.scalar (.numeric (.scalar (.scalar (.localRead 0)))))
    | succ target => simp [parameterSummaryCycleConfig, parameterSummaryCycleModule] at contextAt

theorem parameterSummaryCycle_argumentGraph : RegisterCallGraphWithCallLocals parameterSummaryCycleConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [parameterSummaryCycleConfig, parameterSummaryCycleModule] at contextAt
    subst context
    simp [parameterSummaryCycleConfig, parameterSummaryCycleModule] at implementationAt
    subst implementation
    simp [parameterSummaryCycleEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [parameterSummaryCycleConfig, parameterSummaryCycleModule] at contextAt
      subst context
      simp [parameterSummaryCycleConfig, parameterSummaryCycleModule] at implementationAt
      subst implementation
      simp [parameterSummaryCycleHelper] at parameters
    | succ target => simp [parameterSummaryCycleConfig, parameterSummaryCycleModule] at contextAt

theorem parameterSummaryCycle_module_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld parameterSummaryCycleConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel parameterSummaryCycleConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel parameterSummaryCycleConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let accepted := acceptedModule parameterSummaryCycleConfig parameterSummaryCycle_validated
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩
  have initial : InitialGlobalsOutcome fuel parameterSummaryCycleConfig := by
    apply singleScalarInitialGlobalsOutcome fuel parameterSummaryCycleConfig accepted descriptor (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
    intro names roots typingAfter rootsAfter frame activated world source checked
    cases fuel with
    | zero =>
      simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨declaredRootTypes parameterSummaryCycleModule, (fun _ => False), [], (fun _ _ found => found), world, source.futureGlobals, trivial⟩
    | succ fuel =>
      let context : Context := ⟨1, "cycle", [], [[]], []⟩
      let parameter : Param := ⟨0, .byValue⟩
      have form : UnaryRegisterExpression parameterSummaryCycleConfig .i64 (.lit .i64 7) :=
        .scalar (.numeric (.scalar (.scalar (.integer .i64 7))))
      obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, result⟩ :=
        invokeCall_parameterizedLocalSummaryGraph_allFuel fuel parameterSummaryCycleConfig .i64 accepted parameterSummaryCycle_graph parameterSummaryCycle_argumentGraph
          frame activated [] (declaredRootTypes parameterSummaryCycleModule) (fun _ => False) [] [] 1 0 context parameterSummaryCycleHelper parameter (.lit .i64 7)
          world source (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (.operand form) 4094 (by rfl) roots typingAfter rootsAfter checked
      obtain ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueActs, valueScopes, valueWorld, valueClear, valueResult⟩ :=
        evalValue_registerCall_withArguments_fromInvoke fuel parameterSummaryCycleConfig 0 frame.interpretation.environment activated []
          (declaredRootTypes parameterSummaryCycleModule) [] [] 1 context parameterSummaryCycleHelper [.byVal (.lit .i64 7)] (.int .i64) 0
          (by rfl) (by rfl) (by rfl) ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, result⟩
      exact ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueWorld, valueClear, valueResult⟩
  apply acceptedModuleFromGlobals_allFuel fuel parameterSummaryCycleConfig accepted ⟨0, "entry", [], [], []⟩ parameterSummaryCycleEntry initial (by rfl) (by rfl)
  · exact .nil
  · simp [parameterSummaryCycleEntry, Block.stmts]
  · simp [parameterSummaryCycleEntry, Block.stmts]
  · simp [parameterSummaryCycleEntry, Block.stmts]
  · simp [parameterSummaryCycleEntry, Block.stmts]
  · rfl

#print axioms parameterSummaryCycle_module_allFuel
#print axioms parameterSummaryCycle_argumentGraph
#print axioms parameterSummaryCycle_graph
#print axioms parameterSummaryCycle_actual_timeout
#print axioms parameterSummaryCycle_validated
end Goose.Proofs.ConstructionAcceptedExecution
