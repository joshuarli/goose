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

private def parameterNestedCycleSummary : Summary := ⟨[.param 0], [], [], [], [], [], [], [], false, false⟩
private def parameterNestedCycleEntrySummary : Summary := ⟨[], [], [], [], [], [], [], [], false, false⟩
private def parameterNestedCycleEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .known parameterNestedCycleEntrySummary⟩
private def parameterNestedCycleHelper : Impl := ⟨"cycle", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.call 1 [.byVal (.call 1 [.byVal (.read (.var 0))] 0)] 0)), .known parameterNestedCycleSummary⟩
private def parameterNestedCycleModule : Module := ⟨#["parameter-nested-cycle.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩], #[parameterNestedCycleEntry, parameterNestedCycleHelper],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "cycle", [], [[]], []⟩], 0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def parameterNestedCycleConfig : EvalConfig := ⟨.release, parameterNestedCycleModule⟩

theorem parameterNestedCycle_validated : validate parameterNestedCycleModule = .ok () := by cbv

private def parameterNestedCycleIsTimeout : Bool :=
  match runModule 40 parameterNestedCycleConfig .initial with
  | .stop .timeout _ => true
  | _ => false

theorem parameterNestedCycle_actual_timeout : parameterNestedCycleIsTimeout = true := by decide +kernel

theorem parameterNestedCycle_graph : RecursiveParameterGraph parameterNestedCycleConfig .i64 := by
  intro target context implementation parameter contextAt implementationAt parameters mode results
  cases target with
  | zero =>
    simp [parameterNestedCycleConfig, parameterNestedCycleModule] at contextAt
    subst context
    simp [parameterNestedCycleConfig, parameterNestedCycleModule] at implementationAt
    subst implementation
    simp [parameterNestedCycleEntry] at parameters
  | succ target =>
    cases target with
    | zero =>
      simp [parameterNestedCycleConfig, parameterNestedCycleModule] at contextAt
      subst context
      simp [parameterNestedCycleConfig, parameterNestedCycleModule] at implementationAt
      subst implementation
      have same : parameter = ⟨0, .byValue⟩ := by simpa [parameterNestedCycleHelper] using parameters.symm
      subst parameter
      apply Or.inr
      apply Or.inr
      refine ⟨⟨"value", .int .i64, .immutable, 0, 0⟩, parameterNestedCycleSummary, 1, 0,
        ⟨1, "cycle", [], [[]], []⟩, parameterNestedCycleHelper, ⟨0, .byValue⟩,
        ⟨"value", .int .i64, .immutable, 0, 0⟩, parameterNestedCycleSummary, .call 1 [.byVal (.read (.var 0))] 0,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | exact (.call 1 0 ⟨1, "cycle", [], [[]], []⟩ parameterNestedCycleHelper ⟨0, .byValue⟩
        ⟨"value", .int .i64, .immutable, 0, 0⟩ parameterNestedCycleSummary rfl rfl rfl rfl rfl rfl rfl rfl
        (.localRead 0 ⟨"value", .int .i64, .immutable, 0, 0⟩ rfl rfl))
    | succ target => simp [parameterNestedCycleConfig, parameterNestedCycleModule] at contextAt


theorem parameterNestedCycle_module_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld parameterNestedCycleConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel parameterNestedCycleConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel parameterNestedCycleConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let accepted := acceptedModule parameterNestedCycleConfig parameterNestedCycle_validated
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩
  have initial : InitialGlobalsOutcome fuel parameterNestedCycleConfig := by
    apply singleScalarInitialGlobalsOutcome fuel parameterNestedCycleConfig accepted descriptor (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
    intro names roots typingAfter rootsAfter frame activated world source checked
    cases fuel with
    | zero =>
      simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨declaredRootTypes parameterNestedCycleModule, (fun _ => False), [], (fun _ _ found => found), world, source.futureGlobals, trivial⟩
    | succ fuel =>
      let context : Context := ⟨1, "cycle", [], [[]], []⟩
      let parameter : Param := ⟨0, .byValue⟩
      have form : RecursiveArgumentExpression parameterNestedCycleConfig .i64 frame.source.impl (.lit .i64 7) := .literal 7
      obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, result⟩ :=
        invokeCall_recursiveParameterGraph_allFuel fuel parameterNestedCycleConfig .i64 accepted parameterNestedCycle_graph
          frame activated [] (declaredRootTypes parameterNestedCycleModule) (fun _ => False) [] [] 1 0 context parameterNestedCycleHelper parameter (.lit .i64 7)
          world source (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) form 4094 (by rfl) roots typingAfter rootsAfter checked
      obtain ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueActs, valueScopes, valueWorld, valueClear, valueResult⟩ :=
        evalValue_registerCall_withArguments_fromInvoke fuel parameterNestedCycleConfig 0 frame.interpretation.environment activated []
          (declaredRootTypes parameterNestedCycleModule) [] [] 1 context parameterNestedCycleHelper [.byVal (.lit .i64 7)] (.int .i64) 0
          (by rfl) (by rfl) (by rfl) ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, result⟩
      exact ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueWorld, valueClear, valueResult⟩
  apply acceptedModuleFromGlobals_allFuel fuel parameterNestedCycleConfig accepted ⟨0, "entry", [], [], []⟩ parameterNestedCycleEntry initial (by rfl) (by rfl)
  · exact .nil
  · simp [parameterNestedCycleEntry, Block.stmts]
  · simp [parameterNestedCycleEntry, Block.stmts]
  · simp [parameterNestedCycleEntry, Block.stmts]
  · simp [parameterNestedCycleEntry, Block.stmts]
  · rfl

#print axioms parameterNestedCycle_module_allFuel
#print axioms parameterNestedCycle_graph
#print axioms parameterNestedCycle_actual_timeout
#print axioms parameterNestedCycle_validated
end Goose.Proofs.ConstructionAcceptedExecution
