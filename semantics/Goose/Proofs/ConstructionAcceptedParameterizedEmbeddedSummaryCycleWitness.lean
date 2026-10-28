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

private def parameterEmbeddedSummaryCycleSummary : Summary := ⟨[.param 0], [], [], [], [], [], [], [], true, false⟩
private def parameterEmbeddedSummaryCycleEntrySummary : Summary := ⟨[], [], [], [], [], [], [], [], true, false⟩
private def parameterEmbeddedSummaryCycleEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .known parameterEmbeddedSummaryCycleEntrySummary⟩
private def parameterEmbeddedSummaryCycleHelper : Impl := ⟨"cycle", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.call 1 [.byVal (.bin .add (.call 2 [] 0) (.read (.var 0)) 0)] 0)), .known parameterEmbeddedSummaryCycleSummary⟩
private def parameterEmbeddedSummaryCycleLeaf : Impl := ⟨"leaf", #[], #[⟨.int .i64, .register, none⟩], #[],
  .mk 0 [] (some (.lit .i64 1)), .known parameterEmbeddedSummaryCycleEntrySummary⟩
private def parameterEmbeddedSummaryCycleModule : Module := ⟨#["parameter-embedded-summary-cycle.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩], #[parameterEmbeddedSummaryCycleEntry, parameterEmbeddedSummaryCycleHelper, parameterEmbeddedSummaryCycleLeaf],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "cycle", [], [[]], []⟩, ⟨2, "leaf", [], [[]], []⟩], 0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def parameterEmbeddedSummaryCycleConfig : EvalConfig := ⟨.release, parameterEmbeddedSummaryCycleModule⟩

theorem parameterEmbeddedSummaryCycle_validated : validate parameterEmbeddedSummaryCycleModule = .ok () := by cbv

private def parameterEmbeddedSummaryCycleIsTimeout : Bool :=
  match runModule 40 parameterEmbeddedSummaryCycleConfig .initial with
  | .stop .timeout _ => true
  | _ => false

theorem parameterEmbeddedSummaryCycle_actual_timeout : parameterEmbeddedSummaryCycleIsTimeout = true := by decide +kernel

theorem parameterEmbeddedSummaryCycle_graph : ParameterizedRegisterSummaryRegisterGraph parameterEmbeddedSummaryCycleConfig .i64 := by
  intro target context implementation parameter contextAt implementationAt parameters mode results
  cases target with
  | zero =>
    simp [parameterEmbeddedSummaryCycleConfig, parameterEmbeddedSummaryCycleModule] at contextAt
    subst context
    simp [parameterEmbeddedSummaryCycleConfig, parameterEmbeddedSummaryCycleModule] at implementationAt
    subst implementation
    simp [parameterEmbeddedSummaryCycleEntry] at parameters
  | succ target =>
    cases target with
    | zero =>
      simp [parameterEmbeddedSummaryCycleConfig, parameterEmbeddedSummaryCycleModule] at contextAt
      subst context
      simp [parameterEmbeddedSummaryCycleConfig, parameterEmbeddedSummaryCycleModule] at implementationAt
      subst implementation
      have same : parameter = ⟨0, .byValue⟩ := by simpa [parameterEmbeddedSummaryCycleHelper] using parameters.symm
      subst parameter
      apply Or.inr
      apply Or.inr
      refine ⟨⟨"value", .int .i64, .immutable, 0, 0⟩, parameterEmbeddedSummaryCycleSummary, 1, 0,
        ⟨1, "cycle", [], [[]], []⟩, parameterEmbeddedSummaryCycleHelper, ⟨0, .byValue⟩,
        ⟨"value", .int .i64, .immutable, 0, 0⟩, .bin .add (.call 2 [] 0) (.read (.var 0)) 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | exact Or.inr ⟨Or.inr ⟨.add, .call 2 [] 0, .read (.var 0), 0, rfl⟩, parameterEmbeddedSummaryCycleSummary, rfl⟩ | exact .binary .add 0 (.operand (.call 2 0 ⟨2, "leaf", [], [[]], []⟩ parameterEmbeddedSummaryCycleLeaf rfl rfl rfl rfl)) (.operand (.scalar (.numeric (.scalar (.scalar (.localRead 0))))))
    | succ target =>
      cases target with
      | zero =>
        simp [parameterEmbeddedSummaryCycleConfig, parameterEmbeddedSummaryCycleModule] at contextAt
        subst context
        simp [parameterEmbeddedSummaryCycleConfig, parameterEmbeddedSummaryCycleModule] at implementationAt
        subst implementation
        simp [parameterEmbeddedSummaryCycleLeaf] at parameters
      | succ target => simp [parameterEmbeddedSummaryCycleConfig, parameterEmbeddedSummaryCycleModule] at contextAt

theorem parameterEmbeddedSummaryCycle_argumentGraph : RegisterCallGraphWithCallLocals parameterEmbeddedSummaryCycleConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [parameterEmbeddedSummaryCycleConfig, parameterEmbeddedSummaryCycleModule] at contextAt
    subst context
    simp [parameterEmbeddedSummaryCycleConfig, parameterEmbeddedSummaryCycleModule] at implementationAt
    subst implementation
    simp [parameterEmbeddedSummaryCycleEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [parameterEmbeddedSummaryCycleConfig, parameterEmbeddedSummaryCycleModule] at contextAt
      subst context
      simp [parameterEmbeddedSummaryCycleConfig, parameterEmbeddedSummaryCycleModule] at implementationAt
      subst implementation
      simp [parameterEmbeddedSummaryCycleHelper] at parameters
    | succ target =>
      cases target with
      | zero =>
        simp [parameterEmbeddedSummaryCycleConfig, parameterEmbeddedSummaryCycleModule] at contextAt
        subst context
        simp [parameterEmbeddedSummaryCycleConfig, parameterEmbeddedSummaryCycleModule] at implementationAt
        subst implementation
        apply Or.inl
        refine ⟨_, rfl, Or.inl ⟨0, [], .lit .i64 1, rfl, .nil, ?_, ?_⟩⟩
        · repeat constructor
        · intro id expression origin member
          cases member
      | succ target => simp [parameterEmbeddedSummaryCycleConfig, parameterEmbeddedSummaryCycleModule] at contextAt

theorem parameterEmbeddedSummaryCycle_module_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld parameterEmbeddedSummaryCycleConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel parameterEmbeddedSummaryCycleConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel parameterEmbeddedSummaryCycleConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let accepted := acceptedModule parameterEmbeddedSummaryCycleConfig parameterEmbeddedSummaryCycle_validated
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩
  have initial : InitialGlobalsOutcome fuel parameterEmbeddedSummaryCycleConfig := by
    apply singleScalarInitialGlobalsOutcome fuel parameterEmbeddedSummaryCycleConfig accepted descriptor (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
    intro names roots typingAfter rootsAfter frame activated world source checked
    cases fuel with
    | zero =>
      simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨declaredRootTypes parameterEmbeddedSummaryCycleModule, (fun _ => False), [], (fun _ _ found => found), world, source.futureGlobals, trivial⟩
    | succ fuel =>
      let context : Context := ⟨1, "cycle", [], [[]], []⟩
      let parameter : Param := ⟨0, .byValue⟩
      have form : UnaryRegisterExpression parameterEmbeddedSummaryCycleConfig .i64 (.lit .i64 7) :=
        .scalar (.numeric (.scalar (.scalar (.integer .i64 7))))
      obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, result⟩ :=
        invokeCall_parameterizedRegisterSummaryGraph_allFuel fuel parameterEmbeddedSummaryCycleConfig .i64 accepted parameterEmbeddedSummaryCycle_graph parameterEmbeddedSummaryCycle_argumentGraph
          frame activated [] (declaredRootTypes parameterEmbeddedSummaryCycleModule) (fun _ => False) [] [] 1 0 context parameterEmbeddedSummaryCycleHelper parameter (.lit .i64 7)
          world source (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (.operand form) 4094 (by rfl) roots typingAfter rootsAfter checked
      obtain ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueActs, valueScopes, valueWorld, valueClear, valueResult⟩ :=
        evalValue_registerCall_withArguments_fromInvoke fuel parameterEmbeddedSummaryCycleConfig 0 frame.interpretation.environment activated []
          (declaredRootTypes parameterEmbeddedSummaryCycleModule) [] [] 1 context parameterEmbeddedSummaryCycleHelper [.byVal (.lit .i64 7)] (.int .i64) 0
          (by rfl) (by rfl) (by rfl) ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, result⟩
      exact ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueWorld, valueClear, valueResult⟩
  apply acceptedModuleFromGlobals_allFuel fuel parameterEmbeddedSummaryCycleConfig accepted ⟨0, "entry", [], [], []⟩ parameterEmbeddedSummaryCycleEntry initial (by rfl) (by rfl)
  · exact .nil
  · simp [parameterEmbeddedSummaryCycleEntry, Block.stmts]
  · simp [parameterEmbeddedSummaryCycleEntry, Block.stmts]
  · simp [parameterEmbeddedSummaryCycleEntry, Block.stmts]
  · simp [parameterEmbeddedSummaryCycleEntry, Block.stmts]
  · rfl

#print axioms parameterEmbeddedSummaryCycle_module_allFuel
#print axioms parameterEmbeddedSummaryCycle_argumentGraph
#print axioms parameterEmbeddedSummaryCycle_graph
#print axioms parameterEmbeddedSummaryCycle_actual_timeout
#print axioms parameterEmbeddedSummaryCycle_validated
end Goose.Proofs.ConstructionAcceptedExecution
