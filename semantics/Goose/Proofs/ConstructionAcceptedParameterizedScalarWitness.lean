import Goose.Proofs.ConstructionAcceptedParameterizedRecursiveGraph
import Goose.Proofs.ConstructionAcceptedRecursiveLocalCallEvaluation
import Goose.Proofs.ConstructionAcceptedSingleScalarGlobal
import Goose.Proofs.ConstructionAcceptedModuleFromGlobals

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

private def parameterScalarSummary : Summary := ⟨[], [], [], [], [], [], [], [], true, false⟩
private def parameterScalarEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .known parameterScalarSummary⟩
private def parameterScalarForward : Impl := ⟨"forward", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.call 2 [.byVal (.read (.var 0))] 0)), .known parameterScalarSummary⟩
private def parameterScalarIdentity : Impl := ⟨"identity", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.bin .add (.read (.var 0)) (.lit .i64 3) 0)), .known parameterScalarSummary⟩
private def parameterScalarModule : Module := ⟨#["parameter-scalar.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩],
  #[parameterScalarEntry, parameterScalarForward, parameterScalarIdentity],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "forward", [], [[]], []⟩, ⟨2, "identity", [], [[]], []⟩], 0,
  #[⟨0, 1, "call"⟩], #[], #[]⟩
private def parameterScalarConfig : EvalConfig := ⟨.release, parameterScalarModule⟩

theorem parameterScalar_validated : validate parameterScalarModule = .ok () := by cbv

theorem parameterScalar_graph : ParameterizedScalarRegisterGraph parameterScalarConfig .i64 := by
  intro target context implementation parameter contextAt implementationAt parameters mode results
  cases target with
  | zero =>
    simp [parameterScalarConfig, parameterScalarModule] at contextAt
    subst context
    simp [parameterScalarConfig, parameterScalarModule] at implementationAt
    subst implementation
    simp [parameterScalarEntry] at parameters
  | succ target =>
    cases target with
    | zero =>
      simp [parameterScalarConfig, parameterScalarModule] at contextAt
      subst context
      simp [parameterScalarConfig, parameterScalarModule] at implementationAt
      subst implementation
      have same : parameter = ⟨0, .byValue⟩ := by simpa [parameterScalarForward] using parameters.symm
      subst parameter
      apply Or.inr
      apply Or.inr
      refine ⟨⟨"value", .int .i64, .immutable, 0, 0⟩, parameterScalarSummary, 2, 0,
        ⟨2, "identity", [], [[]], []⟩, parameterScalarIdentity, ⟨0, .byValue⟩,
        ⟨"value", .int .i64, .immutable, 0, 0⟩, .read (.var 0), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | simp [parameterScalarSummary] | exact .scalar (.numeric (.scalar (.scalar (.localRead 0))))
    | succ target =>
      cases target with
      | zero =>
        simp [parameterScalarConfig, parameterScalarModule] at contextAt
        subst context
        simp [parameterScalarConfig, parameterScalarModule] at implementationAt
        subst implementation
        apply Or.inr
        apply Or.inl
        refine ⟨⟨"value", .int .i64, .immutable, 0, 0⟩, parameterScalarSummary,
          .bin .add (.read (.var 0)) (.lit .i64 3) 0, rfl, rfl, rfl, ?_, rfl, ?_⟩
        · simp [parameterScalarSummary]
        · exact .binary .add 0 (.numeric (.scalar (.scalar (.localRead 0))))
            (.numeric (.scalar (.scalar (.integer .i64 3))))
      | succ target => simp [parameterScalarConfig, parameterScalarModule] at contextAt

theorem parameterScalar_argumentGraph : RegisterCallGraphWithCallLocals parameterScalarConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [parameterScalarConfig, parameterScalarModule] at contextAt
    subst context
    simp [parameterScalarConfig, parameterScalarModule] at implementationAt
    subst implementation
    simp [parameterScalarEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [parameterScalarConfig, parameterScalarModule] at contextAt
      subst context
      simp [parameterScalarConfig, parameterScalarModule] at implementationAt
      subst implementation
      simp [parameterScalarForward] at parameters
    | succ target =>
      cases target with
      | zero =>
        simp [parameterScalarConfig, parameterScalarModule] at contextAt
        subst context
        simp [parameterScalarConfig, parameterScalarModule] at implementationAt
        subst implementation
        simp [parameterScalarIdentity] at parameters
      | succ target => simp [parameterScalarConfig, parameterScalarModule] at contextAt

private def parameterScalarObservation : Option Int :=
  match runModule 50 parameterScalarConfig .initial with
  | .ok () state => match state.objects.lookup (.global 0) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem parameterScalar_result : parameterScalarObservation = some 10 := by decide +kernel

theorem parameterScalar_module_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld parameterScalarConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel parameterScalarConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel parameterScalarConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let accepted := acceptedModule parameterScalarConfig parameterScalar_validated
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩
  have initial : InitialGlobalsOutcome fuel parameterScalarConfig := by
    apply singleScalarInitialGlobalsOutcome fuel parameterScalarConfig accepted descriptor (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
    intro names roots typingAfter rootsAfter frame activated world source checked
    cases fuel with
    | zero =>
      simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨declaredRootTypes parameterScalarModule, (fun _ => False), [], (fun _ _ found => found), world, source.futureGlobals, trivial⟩
    | succ fuel =>
      let context : Context := ⟨1, "forward", [], [[]], []⟩
      let parameter : Param := ⟨0, .byValue⟩
      have form : UnaryRegisterExpression parameterScalarConfig .i64 (.lit .i64 7) :=
        .scalar (.numeric (.scalar (.scalar (.integer .i64 7))))
      obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, result⟩ :=
        invokeCall_parameterizedScalarGraph_allFuel fuel parameterScalarConfig .i64 accepted parameterScalar_graph parameterScalar_argumentGraph
          frame activated [] (declaredRootTypes parameterScalarModule) (fun _ => False) [] [] 1 0 context parameterScalarForward parameter (.lit .i64 7)
          world source (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) form 4094 (by rfl) roots typingAfter rootsAfter checked
      obtain ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueActs, valueScopes, valueWorld, valueClear, valueResult⟩ :=
        evalValue_registerCall_withArguments_fromInvoke fuel parameterScalarConfig 0 frame.interpretation.environment activated []
          (declaredRootTypes parameterScalarModule) [] [] 1 context parameterScalarForward [.byVal (.lit .i64 7)] (.int .i64) 0
          (by rfl) (by rfl) (by rfl) ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, result⟩
      exact ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueWorld, valueClear, valueResult⟩
  apply acceptedModuleFromGlobals_allFuel fuel parameterScalarConfig accepted ⟨0, "entry", [], [], []⟩ parameterScalarEntry initial (by rfl) (by rfl)
  · exact .nil
  · simp [parameterScalarEntry, Block.stmts]
  · simp [parameterScalarEntry, Block.stmts]
  · simp [parameterScalarEntry, Block.stmts]
  · simp [parameterScalarEntry, Block.stmts]
  · rfl

#print axioms parameterScalar_module_allFuel
#print axioms parameterScalar_result
#print axioms parameterScalar_validated
end Goose.Proofs.ConstructionAcceptedExecution
