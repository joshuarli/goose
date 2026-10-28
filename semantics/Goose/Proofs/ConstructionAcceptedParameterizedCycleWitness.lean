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

private def parameterCycleSummary : Summary := ⟨[], [], [], [], [], [], [], [], false, false⟩
private def parameterCycleEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .known parameterCycleSummary⟩
private def parameterCycleHelper : Impl := ⟨"cycle", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.call 1 [.byVal (.read (.var 0))] 0)), .known parameterCycleSummary⟩
private def parameterCycleModule : Module := ⟨#["parameter-cycle.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩], #[parameterCycleEntry, parameterCycleHelper],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "cycle", [], [[]], []⟩], 0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def parameterCycleConfig : EvalConfig := ⟨.release, parameterCycleModule⟩

theorem parameterCycle_validated : validate parameterCycleModule = .ok () := by cbv

private def parameterCycleIsTimeout : Bool :=
  match runModule 40 parameterCycleConfig .initial with
  | .stop .timeout _ => true
  | _ => false

theorem parameterCycle_actual_timeout : parameterCycleIsTimeout = true := by decide +kernel

theorem parameterCycle_callee_source :
    ∃ names argumentRoots middle frame,
      let activated := { ExecutionState.initial with nextAct := ExecutionState.initial.nextAct + 1 }
      rpArgs (scalarGlobalInitializerFrame parameterCycleConfig 0 ExecutionState.initial.nextAct names).source
        [.byVal (.lit .i64 7)] (scalarGlobalInitializerFrame parameterCycleConfig 0 ExecutionState.initial.nextAct names).rootCursor = .ok (argumentRoots, middle) ∧
      frame.phase = .implementation 1 ∧ frame.source.impl = parameterCycleHelper ∧ frame.initialized = 0 ∧
      frame.interpretation = CallInterpretation
        (scalarGlobalInitializerFrame parameterCycleConfig 0 ExecutionState.initial.nextAct names).interpretation
        ⟨1, activated.nextAct, parameterCycleHelper.vars, [], [.register (.int .i64)]⟩ argumentRoots ∧
      implementationBodyFrame parameterCycleConfig frame = frame ∧
      SourceFrameCompatible (acceptedModule parameterCycleConfig parameterCycle_validated) frame ∧
      SourcePosition (acceptedModule parameterCycleConfig parameterCycle_validated) frame (.block parameterCycleHelper.body) ∧
      (∀ result after, rpBlockValue frame.source [] parameterCycleHelper.body frame.rootCursor = .ok (result, after) →
        GlobalEffectsAvailable frame.interpretation 0 after.eff) := by
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩
  obtain ⟨names, roots, typingAfter, rootsAfter, world, source, checked⟩ :=
    accepted_nestedGlobal_checked parameterCycleConfig (acceptedModule parameterCycleConfig parameterCycle_validated) 0 descriptor .initial []
      (declaredRootTypes parameterCycleModule) (fun _ => False) (initial_acceptedWorld parameterCycleConfig parameterCycle_validated)
      (futureGlobalsClear_initial parameterCycleConfig) (by rfl) (Or.inl ⟨.i64, rfl⟩)
  let caller := scalarGlobalInitializerFrame parameterCycleConfig 0 ExecutionState.initial.nextAct names
  let activated := { ExecutionState.initial with nextAct := ExecutionState.initial.nextAct + 1 }
  let context : Context := ⟨1, "cycle", [], [[]], []⟩
  let parameter : Param := ⟨0, .byValue⟩
  obtain ⟨argumentRoots, middle, frame, arguments, phase, impl, initialized, interpretation, bodyFrame, compatible, position, effects⟩ :=
    acceptedSingleByValueCalleeSource parameterCycleConfig (acceptedModule parameterCycleConfig parameterCycle_validated)
      caller activated (declaredRootTypes parameterCycleModule) 1 0 context parameterCycleHelper parameter (.lit .i64 7) [.register (.int .i64)]
      source (by rfl) (by rfl) (by rfl) parameterCycleSummary (by rfl) (by simp [parameterCycleSummary])
      (.int .i64) roots typingAfter rootsAfter checked
  refine ⟨names, argumentRoots, middle, frame, arguments, phase, impl, initialized, interpretation, bodyFrame, compatible, position, ?_⟩
  simpa [initialized, caller, scalarGlobalInitializerFrame] using effects

theorem parameterCycle_recursive_tail_checked :
    ∃ frame roots typingAfter rootsAfter,
      let activated := { ExecutionState.initial with nextAct := ExecutionState.initial.nextAct + 1 }
      CheckedValue (entryStatementsFrame parameterCycleConfig frame activated.nextScope)
        (.call 1 [.byVal (.read (.var 0))] 0) (.int .i64) roots typingAfter rootsAfter := by
  obtain ⟨names, argumentRoots, middle, frame, arguments, phase, impl, initialized, interpretation, bodyFrame, compatible, position, effects⟩ :=
    parameterCycle_callee_source
  let activated := { ExecutionState.initial with nextAct := ExecutionState.initial.nextAct + 1 }
  have requests : frame.typing.resultRequests = [.register] := by
    have same := congrArg (fun f : ConstructionSourceFrame => f.typing.resultRequests) bodyFrame
    simpa [implementationBodyFrame, impl, parameterCycleHelper] using same.symm
  have contextAt : frame.typing.module.contexts[1]? = some ⟨1, "cycle", [], [[]], []⟩ := by
    rw [compatible.module]
    rfl
  have calleeAt : frame.typing.module.impls[1]? = some parameterCycleHelper := by
    rw [compatible.module]
    rfl
  have body : frame.source.impl.body = ⟨0, [], some (.call 1 [.byVal (.read (.var 0))] 0)⟩ := by
    simp [impl, parameterCycleHelper]
  have position' : SourcePosition (acceptedModule parameterCycleConfig parameterCycle_validated) frame
      (.block ⟨0, [], some (.call 1 [.byVal (.read (.var 0))] 0)⟩) := by
    simpa [parameterCycleHelper] using position
  obtain ⟨tailRoots, tailTypingAfter, tailRootsAfter, checked⟩ :=
    position'.callee_registerCall_withArguments_tail_checked (acceptedModule parameterCycleConfig parameterCycle_validated)
      frame activated 0 1 0 ⟨1, "cycle", [], [[]], []⟩ parameterCycleHelper (.int .i64) [.byVal (.read (.var 0))]
      bodyFrame body contextAt calleeAt (by rfl) (Or.inl ⟨.i64, rfl⟩) requests (by simpa [parameterCycleHelper, initialized] using effects)
  exact ⟨frame, tailRoots, tailTypingAfter, tailRootsAfter, checked⟩

theorem parameterCycle_graph : ParameterizedRegisterTailGraph parameterCycleConfig .i64 := by
  intro target context implementation parameter contextAt implementationAt parameters mode results
  cases target with
  | zero =>
    simp [parameterCycleConfig, parameterCycleModule] at contextAt
    subst context
    simp [parameterCycleConfig, parameterCycleModule] at implementationAt
    subst implementation
    simp [parameterCycleEntry] at parameters
  | succ target =>
    cases target with
    | zero =>
      simp [parameterCycleConfig, parameterCycleModule] at contextAt
      subst context
      simp [parameterCycleConfig, parameterCycleModule] at implementationAt
      subst implementation
      have same : parameter = ⟨0, .byValue⟩ := by simpa [parameterCycleHelper] using parameters.symm
      subst parameter
      refine ⟨⟨"value", .int .i64, .immutable, 0, 0⟩, parameterCycleSummary, 1, 0,
        ⟨1, "cycle", [], [[]], []⟩, parameterCycleHelper, ⟨0, .byValue⟩,
        ⟨"value", .int .i64, .immutable, 0, 0⟩, .read (.var 0), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | simp [parameterCycleSummary] | exact .scalar (.numeric (.scalar (.scalar (.localRead 0))))
    | succ target => simp [parameterCycleConfig, parameterCycleModule] at contextAt

theorem parameterCycle_argumentGraph : RegisterCallGraphWithCallLocals parameterCycleConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [parameterCycleConfig, parameterCycleModule] at contextAt
    subst context
    simp [parameterCycleConfig, parameterCycleModule] at implementationAt
    subst implementation
    simp [parameterCycleEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [parameterCycleConfig, parameterCycleModule] at contextAt
      subst context
      simp [parameterCycleConfig, parameterCycleModule] at implementationAt
      subst implementation
      simp [parameterCycleHelper] at parameters
    | succ target => simp [parameterCycleConfig, parameterCycleModule] at contextAt

theorem parameterCycle_module_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld parameterCycleConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel parameterCycleConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel parameterCycleConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let accepted := acceptedModule parameterCycleConfig parameterCycle_validated
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [.byVal (.lit .i64 7)] 0, 0⟩
  have initial : InitialGlobalsOutcome fuel parameterCycleConfig := by
    apply singleScalarInitialGlobalsOutcome fuel parameterCycleConfig accepted descriptor (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
    intro names roots typingAfter rootsAfter frame activated world source checked
    cases fuel with
    | zero =>
      simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨declaredRootTypes parameterCycleModule, (fun _ => False), [], (fun _ _ found => found), world, source.futureGlobals, trivial⟩
    | succ fuel =>
      let context : Context := ⟨1, "cycle", [], [[]], []⟩
      let parameter : Param := ⟨0, .byValue⟩
      have form : UnaryRegisterExpression parameterCycleConfig .i64 (.lit .i64 7) :=
        .scalar (.numeric (.scalar (.scalar (.integer .i64 7))))
      obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, result⟩ :=
        invokeCall_parameterizedGraph_allFuel fuel parameterCycleConfig .i64 accepted parameterCycle_graph parameterCycle_argumentGraph
          frame activated [] (declaredRootTypes parameterCycleModule) (fun _ => False) [] [] 1 0 context parameterCycleHelper parameter (.lit .i64 7)
          world source (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) form 4094 (by rfl) roots typingAfter rootsAfter checked
      obtain ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueActs, valueScopes, valueWorld, valueClear, valueResult⟩ :=
        evalValue_registerCall_withArguments_fromInvoke fuel parameterCycleConfig 0 frame.interpretation.environment activated []
          (declaredRootTypes parameterCycleModule) [] [] 1 context parameterCycleHelper [.byVal (.lit .i64 7)] (.int .i64) 0
          (by rfl) (by rfl) (by rfl) ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, result⟩
      exact ⟨valueTypes, valueLive, valueAmbient, valueExtend, valueWorld, valueClear, valueResult⟩
  apply acceptedModuleFromGlobals_allFuel fuel parameterCycleConfig accepted ⟨0, "entry", [], [], []⟩ parameterCycleEntry initial (by rfl) (by rfl)
  · exact .nil
  · simp [parameterCycleEntry, Block.stmts]
  · simp [parameterCycleEntry, Block.stmts]
  · simp [parameterCycleEntry, Block.stmts]
  · simp [parameterCycleEntry, Block.stmts]
  · rfl

#print axioms parameterCycle_module_allFuel
#print axioms parameterCycle_argumentGraph
#print axioms parameterCycle_graph
#print axioms parameterCycle_recursive_tail_checked
#print axioms parameterCycle_callee_source
#print axioms parameterCycle_actual_timeout
#print axioms parameterCycle_validated
end Goose.Proofs.ConstructionAcceptedExecution
