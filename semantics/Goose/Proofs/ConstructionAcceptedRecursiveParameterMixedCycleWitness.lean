import Goose.Proofs.ConstructionAcceptedParameterizedFrameEffects
import Goose.Proofs.ConstructionAcceptedRecursiveParameterExecution
import Goose.Proofs.ConstructionAcceptedRecursiveLocalCallEvaluation
import Goose.Proofs.ConstructionAcceptedSingleScalarGlobal
import Goose.Proofs.ConstructionAcceptedModuleFromGlobals
import Goose.Proofs.ConstructionAcceptedNestedGlobal

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

private def parameterMixedCycleSummary : Summary := ⟨[.param 0], [], [], [], [], [], [], [], true, false⟩
private def parameterMixedCycleEntrySummary : Summary := ⟨[], [], [], [], [], [], [], [], false, false⟩
private def parameterMixedCycleEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .known parameterMixedCycleEntrySummary⟩
private def parameterMixedCycleHelper : Impl := ⟨"cycle", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.call 1 [.byVal (.bin .add (.call 1 [.byVal (.read (.var 0))] 0) (.call 2 [] 0) 0)] 0)), .known parameterMixedCycleSummary⟩
private def parameterMixedCycleLeaf : Impl := ⟨"leaf", #[], #[⟨.int .i64, .register, none⟩], #[],
  .mk 0 [] (some (.lit .i64 1)), .known parameterMixedCycleEntrySummary⟩
private def parameterMixedCycleModule : Module := ⟨#["parameter-mixed-cycle.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩], #[parameterMixedCycleEntry, parameterMixedCycleHelper, parameterMixedCycleLeaf],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "cycle", [], [[]], []⟩, ⟨2, "leaf", [], [[]], []⟩], 0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def parameterMixedCycleConfig : EvalConfig := ⟨.release, parameterMixedCycleModule⟩

theorem parameterMixedCycle_validated : validate parameterMixedCycleModule = .ok () := by cbv

private def parameterMixedCycleIsTimeout : Bool :=
  match runModule 40 parameterMixedCycleConfig .initial with
  | .stop .timeout _ => true
  | _ => false

theorem parameterMixedCycle_actual_timeout : parameterMixedCycleIsTimeout = true := by decide +kernel

theorem parameterMixedCycle_zeroGraph : RegisterCallGraphWithCallLocals parameterMixedCycleConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [parameterMixedCycleConfig, parameterMixedCycleModule] at contextAt
    subst context
    simp [parameterMixedCycleConfig, parameterMixedCycleModule] at implementationAt
    subst implementation
    simp [parameterMixedCycleEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [parameterMixedCycleConfig, parameterMixedCycleModule] at contextAt
      subst context
      simp [parameterMixedCycleConfig, parameterMixedCycleModule] at implementationAt
      subst implementation
      simp [parameterMixedCycleHelper] at parameters
    | succ target =>
      cases target with
      | zero =>
        simp [parameterMixedCycleConfig, parameterMixedCycleModule] at contextAt
        subst context
        simp [parameterMixedCycleConfig, parameterMixedCycleModule] at implementationAt
        subst implementation
        apply Or.inl
        refine ⟨_, rfl, Or.inl ⟨0, [], .lit .i64 1, rfl, .nil, ?_, ?_⟩⟩
        · repeat constructor
        · intro id expression origin member
          cases member
      | succ target => simp [parameterMixedCycleConfig, parameterMixedCycleModule] at contextAt

theorem parameterMixedCycle_graph : RecursiveParameterGraph parameterMixedCycleConfig .i64 := by
  intro target context implementation parameter contextAt implementationAt parameters mode results
  cases target with
  | zero =>
    simp [parameterMixedCycleConfig, parameterMixedCycleModule] at contextAt
    subst context
    simp [parameterMixedCycleConfig, parameterMixedCycleModule] at implementationAt
    subst implementation
    simp [parameterMixedCycleEntry] at parameters
  | succ target =>
    cases target with
    | zero =>
      simp [parameterMixedCycleConfig, parameterMixedCycleModule] at contextAt
      subst context
      simp [parameterMixedCycleConfig, parameterMixedCycleModule] at implementationAt
      subst implementation
      have same : parameter = ⟨0, .byValue⟩ := by simpa [parameterMixedCycleHelper] using parameters.symm
      subst parameter
      apply Or.inr
      apply Or.inr
      refine ⟨⟨"value", .int .i64, .immutable, 0, 0⟩, parameterMixedCycleSummary, 1, 0,
        ⟨1, "cycle", [], [[]], []⟩, parameterMixedCycleHelper, ⟨0, .byValue⟩,
        ⟨"value", .int .i64, .immutable, 0, 0⟩, parameterMixedCycleSummary, .bin .add (.call 1 [.byVal (.read (.var 0))] 0) (.call 2 [] 0) 0,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | exact (.binary .add 0
        (.call 1 0 ⟨1, "cycle", [], [[]], []⟩ parameterMixedCycleHelper ⟨0, .byValue⟩
          ⟨"value", .int .i64, .immutable, 0, 0⟩ parameterMixedCycleSummary rfl rfl rfl rfl rfl rfl rfl rfl
          (.localRead 0 ⟨"value", .int .i64, .immutable, 0, 0⟩ rfl rfl))
        (.zeroCall 2 0 ⟨2, "leaf", [], [[]], []⟩ parameterMixedCycleLeaf rfl rfl rfl rfl parameterMixedCycle_zeroGraph))
    | succ target =>
      cases target with
      | zero =>
        simp [parameterMixedCycleConfig, parameterMixedCycleModule] at contextAt
        subst context
        simp [parameterMixedCycleConfig, parameterMixedCycleModule] at implementationAt
        subst implementation
        simp [parameterMixedCycleLeaf] at parameters
      | succ target => simp [parameterMixedCycleConfig, parameterMixedCycleModule] at contextAt


theorem parameterMixedCycle_module_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld parameterMixedCycleConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel parameterMixedCycleConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel parameterMixedCycleConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let accepted := acceptedModule parameterMixedCycleConfig parameterMixedCycle_validated
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩
  have initial : InitialGlobalsOutcome fuel parameterMixedCycleConfig := by
    apply singleScalarInitialGlobalsOutcome fuel parameterMixedCycleConfig accepted descriptor (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
    intro names roots typingAfter rootsAfter frame activated world source checked
    cases fuel with
    | zero =>
      simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨declaredRootTypes parameterMixedCycleModule, (fun _ => False), [], (fun _ _ found => found), world, source.futureGlobals, trivial⟩
    | succ fuel =>
      let context : Context := ⟨1, "cycle", [], [[]], []⟩
      let parameter : Param := ⟨0, .byValue⟩
      have form : RecursiveArgumentExpression parameterMixedCycleConfig .i64 frame.source.impl (.lit .i64 7) := .literal 7
      obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, result⟩ :=
        invokeCall_recursiveParameterGraph_allFuel fuel parameterMixedCycleConfig .i64 accepted parameterMixedCycle_graph
          frame activated [] (declaredRootTypes parameterMixedCycleModule) (fun _ => False) [] [] 1 0 context parameterMixedCycleHelper parameter (.lit .i64 7)
          world source (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) form 4094 (by rfl) roots typingAfter rootsAfter checked
      obtain ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueActs, valueScopes, valueWorld, valueClear, valueResult⟩ :=
        evalValue_registerCall_withArguments_fromInvoke fuel parameterMixedCycleConfig 0 frame.interpretation.environment activated []
          (declaredRootTypes parameterMixedCycleModule) [] [] 1 context parameterMixedCycleHelper [.byVal (.lit .i64 7)] (.int .i64) 0
          (by rfl) (by rfl) (by rfl) ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, result⟩
      exact ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueWorld, valueClear, valueResult⟩
  apply acceptedModuleFromGlobals_allFuel fuel parameterMixedCycleConfig accepted ⟨0, "entry", [], [], []⟩ parameterMixedCycleEntry initial (by rfl) (by rfl)
  · exact .nil
  · simp [parameterMixedCycleEntry, Block.stmts]
  · simp [parameterMixedCycleEntry, Block.stmts]
  · simp [parameterMixedCycleEntry, Block.stmts]
  · simp [parameterMixedCycleEntry, Block.stmts]
  · rfl

#print axioms parameterMixedCycle_module_allFuel
#print axioms parameterMixedCycle_zeroGraph
#print axioms parameterMixedCycle_graph
#print axioms parameterMixedCycle_actual_timeout
#print axioms parameterMixedCycle_validated
end Goose.Proofs.ConstructionAcceptedExecution
