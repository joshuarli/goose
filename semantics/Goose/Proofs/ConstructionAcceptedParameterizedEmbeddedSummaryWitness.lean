import Goose.Proofs.ConstructionAcceptedParameterizedRecursiveGraph
import Goose.Proofs.ConstructionAcceptedRecursiveLocalCallEvaluation
import Goose.Proofs.ConstructionAcceptedSingleScalarGlobal
import Goose.Proofs.ConstructionAcceptedModuleFromGlobals

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

private def parameterEmbeddedSummarySummary : Summary := ⟨[], [], [], [], [], [], [], [], true, false⟩
private def parameterEmbeddedSummaryForwardSummary : Summary := ⟨[.param 0], [], [], [], [], [], [], [], true, false⟩
private def parameterEmbeddedSummaryEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .known parameterEmbeddedSummarySummary⟩
private def parameterEmbeddedSummaryForward : Impl := ⟨"forward", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.call 2 [.byVal (.bin .add (.call 3 [] 0) (.read (.var 0)) 0)] 0)), .known parameterEmbeddedSummaryForwardSummary⟩
private def parameterEmbeddedSummaryIdentity : Impl := ⟨"identity", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.bin .add (.read (.var 0)) (.lit .i64 3) 0)), .known parameterEmbeddedSummarySummary⟩
private def parameterEmbeddedSummaryLeaf : Impl := ⟨"leaf", #[], #[⟨.int .i64, .register, none⟩], #[],
  .mk 0 [] (some (.lit .i64 7)), .known parameterEmbeddedSummarySummary⟩
private def parameterEmbeddedSummaryModule : Module := ⟨#["parameter-embedded-summary.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩],
  #[parameterEmbeddedSummaryEntry, parameterEmbeddedSummaryForward, parameterEmbeddedSummaryIdentity, parameterEmbeddedSummaryLeaf],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "forward", [], [[]], []⟩, ⟨2, "identity", [], [[]], []⟩, ⟨3, "leaf", [], [[]], []⟩], 0,
  #[⟨0, 1, "call"⟩], #[], #[]⟩
private def parameterEmbeddedSummaryConfig : EvalConfig := ⟨.release, parameterEmbeddedSummaryModule⟩

theorem parameterEmbeddedSummary_validated : validate parameterEmbeddedSummaryModule = .ok () := by cbv

theorem parameterEmbeddedSummary_graph : ParameterizedRegisterSummaryRegisterGraph parameterEmbeddedSummaryConfig .i64 := by
  intro target context implementation parameter contextAt implementationAt parameters mode results
  cases target with
  | zero =>
    simp [parameterEmbeddedSummaryConfig, parameterEmbeddedSummaryModule] at contextAt
    subst context
    simp [parameterEmbeddedSummaryConfig, parameterEmbeddedSummaryModule] at implementationAt
    subst implementation
    simp [parameterEmbeddedSummaryEntry] at parameters
  | succ target =>
    cases target with
    | zero =>
      simp [parameterEmbeddedSummaryConfig, parameterEmbeddedSummaryModule] at contextAt
      subst context
      simp [parameterEmbeddedSummaryConfig, parameterEmbeddedSummaryModule] at implementationAt
      subst implementation
      have same : parameter = ⟨0, .byValue⟩ := by simpa [parameterEmbeddedSummaryForward] using parameters.symm
      subst parameter
      apply Or.inr
      apply Or.inr
      refine ⟨⟨"value", .int .i64, .immutable, 0, 0⟩, parameterEmbeddedSummaryForwardSummary, 2, 0,
        ⟨2, "identity", [], [[]], []⟩, parameterEmbeddedSummaryIdentity, ⟨0, .byValue⟩,
        ⟨"value", .int .i64, .immutable, 0, 0⟩, .bin .add (.call 3 [] 0) (.read (.var 0)) 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | exact Or.inr ⟨Or.inr ⟨.add, .call 3 [] 0, .read (.var 0), 0, rfl⟩, parameterEmbeddedSummarySummary, rfl⟩ | simp [parameterEmbeddedSummarySummary] | exact (.binary .add 0 (.operand (.call 3 0 ⟨3, "leaf", [], [[]], []⟩ parameterEmbeddedSummaryLeaf rfl rfl rfl rfl)) (.operand (.scalar (.numeric (.scalar (.scalar (.localRead 0)))))))
    | succ target =>
      cases target with
      | zero =>
        simp [parameterEmbeddedSummaryConfig, parameterEmbeddedSummaryModule] at contextAt
        subst context
        simp [parameterEmbeddedSummaryConfig, parameterEmbeddedSummaryModule] at implementationAt
        subst implementation
        apply Or.inr
        apply Or.inl
        refine ⟨⟨"value", .int .i64, .immutable, 0, 0⟩, parameterEmbeddedSummarySummary,
          .bin .add (.read (.var 0)) (.lit .i64 3) 0, rfl, rfl, rfl, rfl, ?_⟩
        · exact .binary .add 0 (.numeric (.scalar (.scalar (.localRead 0))))
            (.numeric (.scalar (.scalar (.integer .i64 3))))
      | succ target =>
        cases target with
        | zero =>
          simp [parameterEmbeddedSummaryConfig, parameterEmbeddedSummaryModule] at contextAt
          subst context
          simp [parameterEmbeddedSummaryConfig, parameterEmbeddedSummaryModule] at implementationAt
          subst implementation
          simp [parameterEmbeddedSummaryLeaf] at parameters
        | succ target => simp [parameterEmbeddedSummaryConfig, parameterEmbeddedSummaryModule] at contextAt

theorem parameterEmbeddedSummary_argumentGraph : RegisterCallGraphWithCallLocals parameterEmbeddedSummaryConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [parameterEmbeddedSummaryConfig, parameterEmbeddedSummaryModule] at contextAt
    subst context
    simp [parameterEmbeddedSummaryConfig, parameterEmbeddedSummaryModule] at implementationAt
    subst implementation
    simp [parameterEmbeddedSummaryEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [parameterEmbeddedSummaryConfig, parameterEmbeddedSummaryModule] at contextAt
      subst context
      simp [parameterEmbeddedSummaryConfig, parameterEmbeddedSummaryModule] at implementationAt
      subst implementation
      simp [parameterEmbeddedSummaryForward] at parameters
    | succ target =>
      cases target with
      | zero =>
        simp [parameterEmbeddedSummaryConfig, parameterEmbeddedSummaryModule] at contextAt
        subst context
        simp [parameterEmbeddedSummaryConfig, parameterEmbeddedSummaryModule] at implementationAt
        subst implementation
        simp [parameterEmbeddedSummaryIdentity] at parameters
      | succ target =>
        cases target with
        | zero =>
          simp [parameterEmbeddedSummaryConfig, parameterEmbeddedSummaryModule] at contextAt
          subst context
          simp [parameterEmbeddedSummaryConfig, parameterEmbeddedSummaryModule] at implementationAt
          subst implementation
          apply Or.inl
          refine ⟨_, rfl, Or.inl ⟨0, [], .lit .i64 7, rfl, .nil, ?_, ?_⟩⟩
          · repeat constructor
          · intro id expression origin member
            cases member
        | succ target => simp [parameterEmbeddedSummaryConfig, parameterEmbeddedSummaryModule] at contextAt

private def parameterEmbeddedSummaryObservation : Option Int :=
  match runModule 50 parameterEmbeddedSummaryConfig .initial with
  | .ok () state => match state.objects.lookup (.global 0) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem parameterEmbeddedSummary_result : parameterEmbeddedSummaryObservation = some 17 := by decide +kernel

theorem parameterEmbeddedSummary_module_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld parameterEmbeddedSummaryConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel parameterEmbeddedSummaryConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel parameterEmbeddedSummaryConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let accepted := acceptedModule parameterEmbeddedSummaryConfig parameterEmbeddedSummary_validated
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩
  have initial : InitialGlobalsOutcome fuel parameterEmbeddedSummaryConfig := by
    apply singleScalarInitialGlobalsOutcome fuel parameterEmbeddedSummaryConfig accepted descriptor (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
    intro names roots typingAfter rootsAfter frame activated world source checked
    cases fuel with
    | zero =>
      simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨declaredRootTypes parameterEmbeddedSummaryModule, (fun _ => False), [], (fun _ _ found => found), world, source.futureGlobals, trivial⟩
    | succ fuel =>
      let context : Context := ⟨1, "forward", [], [[]], []⟩
      let parameter : Param := ⟨0, .byValue⟩
      have form : RegisterArithmeticExpression parameterEmbeddedSummaryConfig .i64 (.lit .i64 7) :=
        .operand (.scalar (.numeric (.scalar (.scalar (.integer .i64 7)))))
      obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, result⟩ :=
        invokeCall_parameterizedRegisterSummaryGraph_allFuel fuel parameterEmbeddedSummaryConfig .i64 accepted parameterEmbeddedSummary_graph parameterEmbeddedSummary_argumentGraph
          frame activated [] (declaredRootTypes parameterEmbeddedSummaryModule) (fun _ => False) [] [] 1 0 context parameterEmbeddedSummaryForward parameter (.lit .i64 7)
          world source (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) form 4094 (by rfl) roots typingAfter rootsAfter checked
      obtain ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueActs, valueScopes, valueWorld, valueClear, valueResult⟩ :=
        evalValue_registerCall_withArguments_fromInvoke fuel parameterEmbeddedSummaryConfig 0 frame.interpretation.environment activated []
          (declaredRootTypes parameterEmbeddedSummaryModule) [] [] 1 context parameterEmbeddedSummaryForward [.byVal (.lit .i64 7)] (.int .i64) 0
          (by rfl) (by rfl) (by rfl) ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, result⟩
      exact ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueWorld, valueClear, valueResult⟩
  apply acceptedModuleFromGlobals_allFuel fuel parameterEmbeddedSummaryConfig accepted ⟨0, "entry", [], [], []⟩ parameterEmbeddedSummaryEntry initial (by rfl) (by rfl)
  · exact .nil
  · simp [parameterEmbeddedSummaryEntry, Block.stmts]
  · simp [parameterEmbeddedSummaryEntry, Block.stmts]
  · simp [parameterEmbeddedSummaryEntry, Block.stmts]
  · simp [parameterEmbeddedSummaryEntry, Block.stmts]
  · rfl

#print axioms parameterEmbeddedSummary_module_allFuel
#print axioms parameterEmbeddedSummary_result
#print axioms parameterEmbeddedSummary_validated
end Goose.Proofs.ConstructionAcceptedExecution
