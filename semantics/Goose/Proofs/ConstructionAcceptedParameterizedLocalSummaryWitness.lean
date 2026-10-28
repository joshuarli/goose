import Goose.Proofs.ConstructionAcceptedParameterizedRecursiveGraph
import Goose.Proofs.ConstructionAcceptedRecursiveLocalCallEvaluation
import Goose.Proofs.ConstructionAcceptedSingleScalarGlobal
import Goose.Proofs.ConstructionAcceptedModuleFromGlobals

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

private def parameterLocalSummarySummary : Summary := ⟨[], [], [], [], [], [], [], [], true, false⟩
private def parameterLocalSummaryLeafSummary : Summary := ⟨[.param 0], [], [], [], [], [], [], [], true, false⟩
private def parameterLocalSummaryForwardSummary : Summary := ⟨[.param 0], [], [], [], [], [], [], [], true, false⟩
private def parameterLocalSummaryEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .known parameterLocalSummarySummary⟩
private def parameterLocalSummaryForward : Impl := ⟨"forward", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.call 2 [.byVal (.read (.var 0))] 0)), .known parameterLocalSummaryForwardSummary⟩
private def parameterLocalSummaryIdentity : Impl := ⟨"identity", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.bin .add (.read (.var 0)) (.lit .i64 3) 0)), .known parameterLocalSummaryLeafSummary⟩
private def parameterLocalSummaryModule : Module := ⟨#["parameter-local-summary.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩],
  #[parameterLocalSummaryEntry, parameterLocalSummaryForward, parameterLocalSummaryIdentity],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "forward", [], [[]], []⟩, ⟨2, "identity", [], [[]], []⟩], 0,
  #[⟨0, 1, "call"⟩], #[], #[]⟩
private def parameterLocalSummaryConfig : EvalConfig := ⟨.release, parameterLocalSummaryModule⟩

theorem parameterLocalSummary_validated : validate parameterLocalSummaryModule = .ok () := by cbv

theorem parameterLocalSummary_graph : ParameterizedLocalSummaryRegisterGraph parameterLocalSummaryConfig .i64 := by
  intro target context implementation parameter contextAt implementationAt parameters mode results
  cases target with
  | zero =>
    simp [parameterLocalSummaryConfig, parameterLocalSummaryModule] at contextAt
    subst context
    simp [parameterLocalSummaryConfig, parameterLocalSummaryModule] at implementationAt
    subst implementation
    simp [parameterLocalSummaryEntry] at parameters
  | succ target =>
    cases target with
    | zero =>
      simp [parameterLocalSummaryConfig, parameterLocalSummaryModule] at contextAt
      subst context
      simp [parameterLocalSummaryConfig, parameterLocalSummaryModule] at implementationAt
      subst implementation
      have same : parameter = ⟨0, .byValue⟩ := by simpa [parameterLocalSummaryForward] using parameters.symm
      subst parameter
      apply Or.inr
      apply Or.inr
      refine ⟨⟨"value", .int .i64, .immutable, 0, 0⟩, parameterLocalSummaryForwardSummary, 2, 0,
        ⟨2, "identity", [], [[]], []⟩, parameterLocalSummaryIdentity, ⟨0, .byValue⟩,
        ⟨"value", .int .i64, .immutable, 0, 0⟩, .read (.var 0), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | exact Or.inr ⟨rfl, parameterLocalSummaryLeafSummary, rfl⟩ | simp [parameterLocalSummarySummary] | exact .operand (.scalar (.numeric (.scalar (.scalar (.localRead 0)))))
    | succ target =>
      cases target with
      | zero =>
        simp [parameterLocalSummaryConfig, parameterLocalSummaryModule] at contextAt
        subst context
        simp [parameterLocalSummaryConfig, parameterLocalSummaryModule] at implementationAt
        subst implementation
        apply Or.inr
        apply Or.inl
        refine ⟨⟨"value", .int .i64, .immutable, 0, 0⟩, parameterLocalSummaryLeafSummary,
          .bin .add (.read (.var 0)) (.lit .i64 3) 0, rfl, rfl, rfl, rfl, ?_⟩
        · exact .binary .add 0 (.numeric (.scalar (.scalar (.localRead 0))))
            (.numeric (.scalar (.scalar (.integer .i64 3))))
      | succ target => simp [parameterLocalSummaryConfig, parameterLocalSummaryModule] at contextAt

theorem parameterLocalSummary_argumentGraph : RegisterCallGraphWithCallLocals parameterLocalSummaryConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [parameterLocalSummaryConfig, parameterLocalSummaryModule] at contextAt
    subst context
    simp [parameterLocalSummaryConfig, parameterLocalSummaryModule] at implementationAt
    subst implementation
    simp [parameterLocalSummaryEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [parameterLocalSummaryConfig, parameterLocalSummaryModule] at contextAt
      subst context
      simp [parameterLocalSummaryConfig, parameterLocalSummaryModule] at implementationAt
      subst implementation
      simp [parameterLocalSummaryForward] at parameters
    | succ target =>
      cases target with
      | zero =>
        simp [parameterLocalSummaryConfig, parameterLocalSummaryModule] at contextAt
        subst context
        simp [parameterLocalSummaryConfig, parameterLocalSummaryModule] at implementationAt
        subst implementation
        simp [parameterLocalSummaryIdentity] at parameters
      | succ target => simp [parameterLocalSummaryConfig, parameterLocalSummaryModule] at contextAt

private def parameterLocalSummaryObservation : Option Int :=
  match runModule 50 parameterLocalSummaryConfig .initial with
  | .ok () state => match state.objects.lookup (.global 0) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem parameterLocalSummary_result : parameterLocalSummaryObservation = some 10 := by decide +kernel

theorem parameterLocalSummary_module_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld parameterLocalSummaryConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel parameterLocalSummaryConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel parameterLocalSummaryConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let accepted := acceptedModule parameterLocalSummaryConfig parameterLocalSummary_validated
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩
  have initial : InitialGlobalsOutcome fuel parameterLocalSummaryConfig := by
    apply singleScalarInitialGlobalsOutcome fuel parameterLocalSummaryConfig accepted descriptor (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
    intro names roots typingAfter rootsAfter frame activated world source checked
    cases fuel with
    | zero =>
      simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨declaredRootTypes parameterLocalSummaryModule, (fun _ => False), [], (fun _ _ found => found), world, source.futureGlobals, trivial⟩
    | succ fuel =>
      let context : Context := ⟨1, "forward", [], [[]], []⟩
      let parameter : Param := ⟨0, .byValue⟩
      have form : UnaryRegisterExpression parameterLocalSummaryConfig .i64 (.lit .i64 7) :=
        .scalar (.numeric (.scalar (.scalar (.integer .i64 7))))
      obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, result⟩ :=
        invokeCall_parameterizedLocalSummaryGraph_allFuel fuel parameterLocalSummaryConfig .i64 accepted parameterLocalSummary_graph parameterLocalSummary_argumentGraph
          frame activated [] (declaredRootTypes parameterLocalSummaryModule) (fun _ => False) [] [] 1 0 context parameterLocalSummaryForward parameter (.lit .i64 7)
          world source (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (.operand form) 4094 (by rfl) roots typingAfter rootsAfter checked
      obtain ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueActs, valueScopes, valueWorld, valueClear, valueResult⟩ :=
        evalValue_registerCall_withArguments_fromInvoke fuel parameterLocalSummaryConfig 0 frame.interpretation.environment activated []
          (declaredRootTypes parameterLocalSummaryModule) [] [] 1 context parameterLocalSummaryForward [.byVal (.lit .i64 7)] (.int .i64) 0
          (by rfl) (by rfl) (by rfl) ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, result⟩
      exact ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueWorld, valueClear, valueResult⟩
  apply acceptedModuleFromGlobals_allFuel fuel parameterLocalSummaryConfig accepted ⟨0, "entry", [], [], []⟩ parameterLocalSummaryEntry initial (by rfl) (by rfl)
  · exact .nil
  · simp [parameterLocalSummaryEntry, Block.stmts]
  · simp [parameterLocalSummaryEntry, Block.stmts]
  · simp [parameterLocalSummaryEntry, Block.stmts]
  · simp [parameterLocalSummaryEntry, Block.stmts]
  · rfl

#print axioms parameterLocalSummary_module_allFuel
#print axioms parameterLocalSummary_result
#print axioms parameterLocalSummary_validated
end Goose.Proofs.ConstructionAcceptedExecution
