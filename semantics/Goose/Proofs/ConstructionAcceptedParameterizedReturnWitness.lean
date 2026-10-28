import Goose.Proofs.ConstructionAcceptedParameterizedRecursiveGraph
import Goose.Proofs.ConstructionAcceptedRecursiveLocalCallEvaluation
import Goose.Proofs.ConstructionAcceptedSingleScalarGlobal
import Goose.Proofs.ConstructionAcceptedModuleFromGlobals

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

private def parameterReturnSummary : Summary := ⟨[], [], [], [], [], [], [], [], false, false⟩
private def parameterReturnEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .known parameterReturnSummary⟩
private def parameterReturnForward : Impl := ⟨"forward", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.call 2 [.byVal (.read (.var 0))] 0)), .known parameterReturnSummary⟩
private def parameterReturnIdentity : Impl := ⟨"identity", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.read (.var 0))), .known parameterReturnSummary⟩
private def parameterReturnModule : Module := ⟨#["parameter-return.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩],
  #[parameterReturnEntry, parameterReturnForward, parameterReturnIdentity],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "forward", [], [[]], []⟩, ⟨2, "identity", [], [[]], []⟩], 0,
  #[⟨0, 1, "call"⟩], #[], #[]⟩
private def parameterReturnConfig : EvalConfig := ⟨.release, parameterReturnModule⟩

theorem parameterReturn_validated : validate parameterReturnModule = .ok () := by cbv

theorem parameterReturn_graph : ParameterizedRegisterGraph parameterReturnConfig .i64 := by
  intro target context implementation parameter contextAt implementationAt parameters mode results
  cases target with
  | zero =>
    simp [parameterReturnConfig, parameterReturnModule] at contextAt
    subst context
    simp [parameterReturnConfig, parameterReturnModule] at implementationAt
    subst implementation
    simp [parameterReturnEntry] at parameters
  | succ target =>
    cases target with
    | zero =>
      simp [parameterReturnConfig, parameterReturnModule] at contextAt
      subst context
      simp [parameterReturnConfig, parameterReturnModule] at implementationAt
      subst implementation
      have same : parameter = ⟨0, .byValue⟩ := by simpa [parameterReturnForward] using parameters.symm
      subst parameter
      apply Or.inr
      refine ⟨⟨"value", .int .i64, .immutable, 0, 0⟩, parameterReturnSummary, 2, 0,
        ⟨2, "identity", [], [[]], []⟩, parameterReturnIdentity, ⟨0, .byValue⟩,
        ⟨"value", .int .i64, .immutable, 0, 0⟩, .read (.var 0), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | simp [parameterReturnSummary] | exact .scalar (.numeric (.scalar (.scalar (.localRead 0))))
    | succ target =>
      cases target with
      | zero =>
        simp [parameterReturnConfig, parameterReturnModule] at contextAt
        subst context
        simp [parameterReturnConfig, parameterReturnModule] at implementationAt
        subst implementation
        apply Or.inl
        exact ⟨⟨"value", .int .i64, .immutable, 0, 0⟩, rfl, rfl, rfl⟩
      | succ target => simp [parameterReturnConfig, parameterReturnModule] at contextAt

theorem parameterReturn_argumentGraph : RegisterCallGraphWithCallLocals parameterReturnConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [parameterReturnConfig, parameterReturnModule] at contextAt
    subst context
    simp [parameterReturnConfig, parameterReturnModule] at implementationAt
    subst implementation
    simp [parameterReturnEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [parameterReturnConfig, parameterReturnModule] at contextAt
      subst context
      simp [parameterReturnConfig, parameterReturnModule] at implementationAt
      subst implementation
      simp [parameterReturnForward] at parameters
    | succ target =>
      cases target with
      | zero =>
        simp [parameterReturnConfig, parameterReturnModule] at contextAt
        subst context
        simp [parameterReturnConfig, parameterReturnModule] at implementationAt
        subst implementation
        simp [parameterReturnIdentity] at parameters
      | succ target => simp [parameterReturnConfig, parameterReturnModule] at contextAt

private def parameterReturnObservation : Option Int :=
  match runModule 50 parameterReturnConfig .initial with
  | .ok () state => match state.objects.lookup (.global 0) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem parameterReturn_result : parameterReturnObservation = some 7 := by decide +kernel

theorem parameterReturn_module_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld parameterReturnConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel parameterReturnConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel parameterReturnConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let accepted := acceptedModule parameterReturnConfig parameterReturn_validated
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩
  have initial : InitialGlobalsOutcome fuel parameterReturnConfig := by
    apply singleScalarInitialGlobalsOutcome fuel parameterReturnConfig accepted descriptor (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
    intro names roots typingAfter rootsAfter frame activated world source checked
    cases fuel with
    | zero =>
      simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨declaredRootTypes parameterReturnModule, (fun _ => False), [], (fun _ _ found => found), world, source.futureGlobals, trivial⟩
    | succ fuel =>
      let context : Context := ⟨1, "forward", [], [[]], []⟩
      let parameter : Param := ⟨0, .byValue⟩
      have form : UnaryRegisterExpression parameterReturnConfig .i64 (.lit .i64 7) :=
        .scalar (.numeric (.scalar (.scalar (.integer .i64 7))))
      obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, result⟩ :=
        invokeCall_parameterizedGeneralGraph_allFuel fuel parameterReturnConfig .i64 accepted parameterReturn_graph parameterReturn_argumentGraph
          frame activated [] (declaredRootTypes parameterReturnModule) (fun _ => False) [] [] 1 0 context parameterReturnForward parameter (.lit .i64 7)
          world source (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) form 4094 (by rfl) roots typingAfter rootsAfter checked
      obtain ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueActs, valueScopes, valueWorld, valueClear, valueResult⟩ :=
        evalValue_registerCall_withArguments_fromInvoke fuel parameterReturnConfig 0 frame.interpretation.environment activated []
          (declaredRootTypes parameterReturnModule) [] [] 1 context parameterReturnForward [.byVal (.lit .i64 7)] (.int .i64) 0
          (by rfl) (by rfl) (by rfl) ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, result⟩
      exact ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueWorld, valueClear, valueResult⟩
  apply acceptedModuleFromGlobals_allFuel fuel parameterReturnConfig accepted ⟨0, "entry", [], [], []⟩ parameterReturnEntry initial (by rfl) (by rfl)
  · exact .nil
  · simp [parameterReturnEntry, Block.stmts]
  · simp [parameterReturnEntry, Block.stmts]
  · simp [parameterReturnEntry, Block.stmts]
  · simp [parameterReturnEntry, Block.stmts]
  · rfl

#print axioms parameterReturn_module_allFuel
#print axioms parameterReturn_result
#print axioms parameterReturn_validated
end Goose.Proofs.ConstructionAcceptedExecution
