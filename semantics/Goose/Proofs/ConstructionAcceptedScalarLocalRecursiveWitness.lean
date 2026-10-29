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

#print axioms parameterLocalPrefix_sourceEffects
#print axioms parameterLocalPrefix_statements
#print axioms parameterLocalPrefix_actual_timeout
#print axioms parameterLocalPrefix_validated
end Goose.Proofs.ConstructionAcceptedExecution
