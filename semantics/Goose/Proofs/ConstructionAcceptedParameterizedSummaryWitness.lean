import Goose.Proofs.ConstructionAcceptedParameterizedRecursiveGraph
import Goose.Proofs.ConstructionAcceptedRecursiveLocalCallEvaluation
import Goose.Proofs.ConstructionAcceptedSingleScalarGlobal
import Goose.Proofs.ConstructionAcceptedModuleFromGlobals

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

private def parameterSummarySummary : Summary := ⟨[], [], [], [], [], [], [], [], true, false⟩
private def parameterSummaryLeafSummary : Summary := ⟨[.param 0], [], [], [], [], [], [], [], true, false⟩
private def parameterSummaryEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .known parameterSummarySummary⟩
private def parameterSummaryForward : Impl := ⟨"forward", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.call 2 [.byVal (.read (.var 0))] 0)), .known parameterSummarySummary⟩
private def parameterSummaryIdentity : Impl := ⟨"identity", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.bin .add (.read (.var 0)) (.lit .i64 3) 0)), .known parameterSummaryLeafSummary⟩
private def parameterSummaryModule : Module := ⟨#["parameter-summary.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩],
  #[parameterSummaryEntry, parameterSummaryForward, parameterSummaryIdentity],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "forward", [], [[]], []⟩, ⟨2, "identity", [], [[]], []⟩], 0,
  #[⟨0, 1, "call"⟩], #[], #[]⟩
private def parameterSummaryConfig : EvalConfig := ⟨.release, parameterSummaryModule⟩

theorem parameterSummary_validated : validate parameterSummaryModule = .ok () := by cbv

theorem parameterSummary_graph : ParameterizedSummaryRegisterGraph parameterSummaryConfig .i64 := by
  intro target context implementation parameter contextAt implementationAt parameters mode results
  cases target with
  | zero =>
    simp [parameterSummaryConfig, parameterSummaryModule] at contextAt
    subst context
    simp [parameterSummaryConfig, parameterSummaryModule] at implementationAt
    subst implementation
    simp [parameterSummaryEntry] at parameters
  | succ target =>
    cases target with
    | zero =>
      simp [parameterSummaryConfig, parameterSummaryModule] at contextAt
      subst context
      simp [parameterSummaryConfig, parameterSummaryModule] at implementationAt
      subst implementation
      have same : parameter = ⟨0, .byValue⟩ := by simpa [parameterSummaryForward] using parameters.symm
      subst parameter
      apply Or.inr
      apply Or.inr
      refine ⟨⟨"value", .int .i64, .immutable, 0, 0⟩, parameterSummarySummary, 2, 0,
        ⟨2, "identity", [], [[]], []⟩, parameterSummaryIdentity, ⟨0, .byValue⟩,
        ⟨"value", .int .i64, .immutable, 0, 0⟩, .read (.var 0), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | simp [parameterSummarySummary] | exact .operand (.scalar (.numeric (.scalar (.scalar (.localRead 0)))))
    | succ target =>
      cases target with
      | zero =>
        simp [parameterSummaryConfig, parameterSummaryModule] at contextAt
        subst context
        simp [parameterSummaryConfig, parameterSummaryModule] at implementationAt
        subst implementation
        apply Or.inr
        apply Or.inl
        refine ⟨⟨"value", .int .i64, .immutable, 0, 0⟩, parameterSummaryLeafSummary,
          .bin .add (.read (.var 0)) (.lit .i64 3) 0, rfl, rfl, rfl, rfl, ?_⟩
        · exact .binary .add 0 (.numeric (.scalar (.scalar (.localRead 0))))
            (.numeric (.scalar (.scalar (.integer .i64 3))))
      | succ target => simp [parameterSummaryConfig, parameterSummaryModule] at contextAt

theorem parameterSummary_argumentGraph : RegisterCallGraphWithCallLocals parameterSummaryConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [parameterSummaryConfig, parameterSummaryModule] at contextAt
    subst context
    simp [parameterSummaryConfig, parameterSummaryModule] at implementationAt
    subst implementation
    simp [parameterSummaryEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [parameterSummaryConfig, parameterSummaryModule] at contextAt
      subst context
      simp [parameterSummaryConfig, parameterSummaryModule] at implementationAt
      subst implementation
      simp [parameterSummaryForward] at parameters
    | succ target =>
      cases target with
      | zero =>
        simp [parameterSummaryConfig, parameterSummaryModule] at contextAt
        subst context
        simp [parameterSummaryConfig, parameterSummaryModule] at implementationAt
        subst implementation
        simp [parameterSummaryIdentity] at parameters
      | succ target => simp [parameterSummaryConfig, parameterSummaryModule] at contextAt

private def parameterSummaryObservation : Option Int :=
  match runModule 50 parameterSummaryConfig .initial with
  | .ok () state => match state.objects.lookup (.global 0) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem parameterSummary_result : parameterSummaryObservation = some 10 := by decide +kernel

theorem parameterSummary_module_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld parameterSummaryConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel parameterSummaryConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel parameterSummaryConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let accepted := acceptedModule parameterSummaryConfig parameterSummary_validated
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩
  have initial : InitialGlobalsOutcome fuel parameterSummaryConfig := by
    apply singleScalarInitialGlobalsOutcome fuel parameterSummaryConfig accepted descriptor (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
    intro names roots typingAfter rootsAfter frame activated world source checked
    cases fuel with
    | zero =>
      simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨declaredRootTypes parameterSummaryModule, (fun _ => False), [], (fun _ _ found => found), world, source.futureGlobals, trivial⟩
    | succ fuel =>
      let context : Context := ⟨1, "forward", [], [[]], []⟩
      let parameter : Param := ⟨0, .byValue⟩
      have form : UnaryRegisterExpression parameterSummaryConfig .i64 (.lit .i64 7) :=
        .scalar (.numeric (.scalar (.scalar (.integer .i64 7))))
      obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, result⟩ :=
        invokeCall_parameterizedSummaryGraph_allFuel fuel parameterSummaryConfig .i64 accepted parameterSummary_graph parameterSummary_argumentGraph
          frame activated [] (declaredRootTypes parameterSummaryModule) (fun _ => False) [] [] 1 0 context parameterSummaryForward parameter (.lit .i64 7)
          world source (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (.operand form) 4094 (by rfl) roots typingAfter rootsAfter checked
      obtain ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueActs, valueScopes, valueWorld, valueClear, valueResult⟩ :=
        evalValue_registerCall_withArguments_fromInvoke fuel parameterSummaryConfig 0 frame.interpretation.environment activated []
          (declaredRootTypes parameterSummaryModule) [] [] 1 context parameterSummaryForward [.byVal (.lit .i64 7)] (.int .i64) 0
          (by rfl) (by rfl) (by rfl) ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, result⟩
      exact ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueWorld, valueClear, valueResult⟩
  apply acceptedModuleFromGlobals_allFuel fuel parameterSummaryConfig accepted ⟨0, "entry", [], [], []⟩ parameterSummaryEntry initial (by rfl) (by rfl)
  · exact .nil
  · simp [parameterSummaryEntry, Block.stmts]
  · simp [parameterSummaryEntry, Block.stmts]
  · simp [parameterSummaryEntry, Block.stmts]
  · simp [parameterSummaryEntry, Block.stmts]
  · rfl

#print axioms parameterSummary_module_allFuel
#print axioms parameterSummary_result
#print axioms parameterSummary_validated
end Goose.Proofs.ConstructionAcceptedExecution
