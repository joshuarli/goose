import Goose.Proofs.ConstructionAcceptedRecursiveParameterPrefixExecution
import Goose.Proofs.ConstructionAcceptedParameterizedFrameEffects
import Goose.Proofs.ConstructionAcceptedScalarLocalRecursiveEffects
import Goose.Proofs.ConstructionAcceptedRecursiveLocalCallEvaluation
import Goose.Proofs.ConstructionAcceptedSingleScalarGlobal
import Goose.Proofs.ConstructionAcceptedModuleFromGlobals
import Goose.Proofs.ConstructionAcceptedNestedGlobal

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

private def parameterLocalPrefixSummary : Summary := ⟨[.param 0], [], [], [], [], [], [], [], false, false⟩
private def parameterLocalPrefixEntrySummary : Summary := ⟨[], [], [], [], [], [], [], [], false, false⟩
private def parameterLocalPrefixEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .known parameterLocalPrefixEntrySummary⟩
private def parameterLocalPrefixHelper : Impl := ⟨"cycle", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩, ⟨"scratch", .int .i64, .immutable, 0, 0⟩], .mk 0 [.letS 1 (.lit .i64 1) 0] (some (.call 1 [.byVal (.read (.var 1))] 0)), .known parameterLocalPrefixSummary⟩
private def parameterLocalPrefixModule : Module := ⟨#["parameter-local-prefix.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩], #[parameterLocalPrefixEntry, parameterLocalPrefixHelper],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "cycle", [], [[]], []⟩], 0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def parameterLocalPrefixConfig : EvalConfig := ⟨.release, parameterLocalPrefixModule⟩

theorem parameterLocalPrefix_validated : validate parameterLocalPrefixModule = .ok () := by cbv

private def parameterLocalPrefixIsTimeout : Bool :=
  match runModule 40 parameterLocalPrefixConfig .initial with
  | .stop .timeout _ => true
  | _ => false

theorem parameterLocalPrefix_actual_timeout : parameterLocalPrefixIsTimeout = true := by decide +kernel

theorem parameterLocalPrefix_statements : ScalarLocalStatements [.letS 1 (.lit .i64 1) 0] := by
  exact .cons 1 (.lit .i64 1) 0 [] (.numeric (.scalar (.scalar (.integer .i64 1)))) .nil

theorem parameterLocalPrefix_sourceEffects :
    ∃ names frame,
      let caller := scalarGlobalInitializerFrame parameterLocalPrefixConfig 0 ExecutionState.initial.nextAct names
      frame.phase = .implementation 1 ∧ frame.source.impl = parameterLocalPrefixHelper ∧ frame.initialized = caller.initialized ∧
      SourceFrameCompatible (acceptedModule parameterLocalPrefixConfig parameterLocalPrefix_validated) frame ∧
      (∀ result after, rpBlockValue (implementationBodyFrame parameterLocalPrefixConfig frame).source [] parameterLocalPrefixHelper.body
        (implementationBodyFrame parameterLocalPrefixConfig frame).rootCursor = .ok (result, after) →
        GlobalEffectsAvailable frame.interpretation frame.initialized after.eff) := by
  let accepted := acceptedModule parameterLocalPrefixConfig parameterLocalPrefix_validated
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩
  obtain ⟨names, roots, typingAfter, rootsAfter, world, source, checked⟩ :=
    accepted_nestedGlobal_checked parameterLocalPrefixConfig accepted 0 descriptor .initial [] (declaredRootTypes parameterLocalPrefixModule)
      (fun _ => False) (initial_acceptedWorld parameterLocalPrefixConfig parameterLocalPrefix_validated) (futureGlobalsClear_initial parameterLocalPrefixConfig)
      (by rfl) (Or.inl ⟨.i64, rfl⟩)
  let caller := scalarGlobalInitializerFrame parameterLocalPrefixConfig 0 ExecutionState.initial.nextAct names
  let activated := { ExecutionState.initial with nextAct := ExecutionState.initial.nextAct + 1 }
  let context : Context := ⟨1, "cycle", [], [[]], []⟩
  let parameter : Param := ⟨0, .byValue⟩
  obtain ⟨argumentRoots, middle, arguments, available⟩ := checked.singleByValue_callEffectsAvailable parameterLocalPrefixConfig caller 1 0 context
    parameterLocalPrefixHelper parameter (.lit .i64 7) (.int .i64) roots typingAfter rootsAfter (by rfl) (by rfl) source.compatible.rootModule (by rfl)
  obtain ⟨frame, phase, impl, aliases, interpretation, initialized, bodyFrame, compatible, allocated, frontier⟩ :=
    acceptedCalleeSourceFrame parameterLocalPrefixConfig accepted caller activated 1 context parameterLocalPrefixHelper argumentRoots [.register (.int .i64)]
      source.compatible source.frontier (by rfl) (by rfl)
  have argumentForm : RecursiveArgumentExpression parameterLocalPrefixConfig .i64 parameterLocalPrefixHelper (.read (.var 1)) :=
    .localRead 1 ⟨"scratch", .int .i64, .immutable, 0, 0⟩ rfl rfl
  have effects := checked.singleByValue_scalarLocalRecursiveBody_effects accepted caller frame 1 context parameterLocalPrefixHelper
    parameter (.lit .i64 7) ⟨1, activated.nextAct, parameterLocalPrefixHelper.vars, [], [.register (.int .i64)]⟩ 0
    (.int .i64) roots typingAfter rootsAfter source.compatible compatible (by rfl) (by rfl) (by rfl) parameterLocalPrefixSummary (by rfl)
    1 0 [.letS 1 (.lit .i64 1) 0] (.read (.var 1)) .i64 context parameterLocalPrefixHelper parameter parameterLocalPrefixSummary
    (by rfl) parameterLocalPrefix_statements argumentForm (by rfl) (by rfl) (by rfl) (by rfl)
    (by
      intro id initializer location member localDescriptor declared
      simp only [List.mem_singleton, Stmt.letS.injEq] at member
      obtain ⟨rfl, rfl, rfl⟩ := member
      simp [parameterLocalPrefixHelper] at declared
      subst localDescriptor
      exact Or.inl ⟨.i64, rfl⟩)
    phase impl initialized
  exact ⟨names, frame, phase, impl, initialized, compatible, effects⟩

theorem parameterLocalPrefix_graph : RecursiveParameterPrefixGraph parameterLocalPrefixConfig .i64 := by
  intro target context implementation parameter contextAt implementationAt parameters mode results
  cases target with
  | zero =>
    simp [parameterLocalPrefixConfig, parameterLocalPrefixModule] at contextAt
    subst context
    simp [parameterLocalPrefixConfig, parameterLocalPrefixModule] at implementationAt
    subst implementation
    simp [parameterLocalPrefixEntry] at parameters
  | succ target =>
    cases target with
    | zero =>
      simp [parameterLocalPrefixConfig, parameterLocalPrefixModule] at contextAt
      subst context
      simp [parameterLocalPrefixConfig, parameterLocalPrefixModule] at implementationAt
      subst implementation
      have same : parameter = ⟨0, .byValue⟩ := by simpa [parameterLocalPrefixHelper] using parameters.symm
      subst parameter
      apply Or.inr
      apply Or.inr
      refine ⟨⟨"value", .int .i64, .immutable, 0, 0⟩, parameterLocalPrefixSummary, 1, 0,
        ⟨1, "cycle", [], [[]], []⟩, parameterLocalPrefixHelper, ⟨0, .byValue⟩,
        ⟨"value", .int .i64, .immutable, 0, 0⟩, parameterLocalPrefixSummary, .read (.var 1),
        [.letS 1 (.lit .i64 1) 0], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | exact (.localRead 1 ⟨"scratch", .int .i64, .immutable, 0, 0⟩ rfl rfl) | exact parameterLocalPrefix_statements | skip
      intro id initializer location member localDescriptor declared
      simp only [List.mem_singleton, Stmt.letS.injEq] at member
      obtain ⟨rfl, rfl, rfl⟩ := member
      simp [parameterLocalPrefixHelper] at declared
      subst localDescriptor
      exact Or.inl ⟨.i64, rfl⟩
    | succ target => simp [parameterLocalPrefixConfig, parameterLocalPrefixModule] at contextAt

theorem parameterLocalPrefix_module_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld parameterLocalPrefixConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel parameterLocalPrefixConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel parameterLocalPrefixConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let accepted := acceptedModule parameterLocalPrefixConfig parameterLocalPrefix_validated
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩
  have initial : InitialGlobalsOutcome fuel parameterLocalPrefixConfig := by
    apply singleScalarInitialGlobalsOutcome fuel parameterLocalPrefixConfig accepted descriptor (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
    intro names roots typingAfter rootsAfter frame activated world source checked
    cases fuel with
    | zero =>
      simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨declaredRootTypes parameterLocalPrefixModule, (fun _ => False), [], (fun _ _ found => found), world, source.futureGlobals, trivial⟩
    | succ fuel =>
      let context : Context := ⟨1, "cycle", [], [[]], []⟩
      let parameter : Param := ⟨0, .byValue⟩
      have form : RecursiveArgumentExpression parameterLocalPrefixConfig .i64 frame.source.impl (.lit .i64 7) := .literal 7
      obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, result⟩ :=
        invokeCall_recursiveParameterPrefixGraph_allFuel fuel parameterLocalPrefixConfig .i64 accepted parameterLocalPrefix_graph
          frame activated [] (declaredRootTypes parameterLocalPrefixModule) (fun _ => False) [] [] 1 0 context parameterLocalPrefixHelper parameter (.lit .i64 7)
          world source (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) form 4094 (by rfl) roots typingAfter rootsAfter checked
      obtain ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueActs, valueScopes, valueWorld, valueClear, valueResult⟩ :=
        evalValue_registerCall_withArguments_fromInvoke fuel parameterLocalPrefixConfig 0 frame.interpretation.environment activated []
          (declaredRootTypes parameterLocalPrefixModule) [] [] 1 context parameterLocalPrefixHelper [.byVal (.lit .i64 7)] (.int .i64) 0
          (by rfl) (by rfl) (by rfl) ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, result⟩
      exact ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueWorld, valueClear, valueResult⟩
  apply acceptedModuleFromGlobals_allFuel fuel parameterLocalPrefixConfig accepted ⟨0, "entry", [], [], []⟩ parameterLocalPrefixEntry initial (by rfl) (by rfl)
  · exact .nil
  · simp [parameterLocalPrefixEntry, Block.stmts]
  · simp [parameterLocalPrefixEntry, Block.stmts]
  · simp [parameterLocalPrefixEntry, Block.stmts]
  · simp [parameterLocalPrefixEntry, Block.stmts]
  · rfl


#print axioms parameterLocalPrefix_module_allFuel
#print axioms parameterLocalPrefix_graph
#print axioms parameterLocalPrefix_sourceEffects
#print axioms parameterLocalPrefix_statements
#print axioms parameterLocalPrefix_actual_timeout
#print axioms parameterLocalPrefix_validated
end Goose.Proofs.ConstructionAcceptedExecution
