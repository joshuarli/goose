import Goose.Proofs.ConstructionAcceptedNestedParameterSource
import Goose.Proofs.ConstructionAcceptedNestedGlobal
import Goose.Proofs.ConstructionAcceptedSingleScalarGlobal
import Goose.Proofs.ConstructionAcceptedNestedScalarCalls
import Goose.Proofs.ConstructionAcceptedModuleFromGlobals

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

private def nestedScalarCallsEntrySummary : Summary := ⟨[], [], [], [], [], [], [], [], true, false⟩
private def nestedScalarCallsHelperSummary : Summary := ⟨[.param 0], [], [], [], [], [], [], [], true, false⟩
private def nestedScalarCallsEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .known nestedScalarCallsEntrySummary⟩
private def nestedScalarCallsHelper : Impl := ⟨"identity", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.bin .add (.read (.var 0)) (.lit .i64 3) 0)), .known nestedScalarCallsHelperSummary⟩
private def nestedScalarCallsExpression : Expr := .bin .add (.call 1 [.byVal (.call 1 [.byVal (.lit .i64 7)] 0)] 0) (.call 1 [.byVal (.lit .i64 2)] 0) 0
private def nestedScalarCallsGlobal : Global := ⟨"answer", .int .i64, .immutable, nestedScalarCallsExpression, 0⟩
private def nestedScalarCallsModule : Module := ⟨#["nested-scalar-calls.goose"], #[.int .i64], #[nestedScalarCallsGlobal],
  #[nestedScalarCallsEntry, nestedScalarCallsHelper], #[⟨0, "entry", [], [], []⟩, ⟨1, "identity", [], [[]], []⟩], 0,
  #[⟨0, 1, "call"⟩], #[], #[]⟩
private def nestedScalarCallsConfig : EvalConfig := ⟨.release, nestedScalarCallsModule⟩

theorem nestedScalarCalls_validated : validate nestedScalarCallsModule = .ok () := by cbv

theorem nestedScalarCalls_sourceForm : NestedParameterExpression nestedScalarCallsConfig .i64 initImpl nestedScalarCallsExpression := by
  unfold nestedScalarCallsExpression
  apply NestedParameterExpression.binary .add 0
  · apply NestedParameterExpression.call 1 0 ⟨1, "identity", [], [[]], []⟩ nestedScalarCallsHelper ⟨0, .byValue⟩ nestedScalarCallsHelperSummary
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    apply NestedParameterExpression.call 1 0 ⟨1, "identity", [], [[]], []⟩ nestedScalarCallsHelper ⟨0, .byValue⟩ nestedScalarCallsHelperSummary
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    exact .literal 7
  · apply NestedParameterExpression.call 1 0 ⟨1, "identity", [], [[]], []⟩ nestedScalarCallsHelper ⟨0, .byValue⟩ nestedScalarCallsHelperSummary
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    exact .literal 2

theorem nestedScalarCalls_checkedRoots :
    ∃ names roots typingAfter rootsAfter,
      let frame := scalarGlobalInitializerFrame nestedScalarCallsConfig 0 ExecutionState.initial.nextAct names
      CheckedValue frame nestedScalarCallsExpression (.int .i64) roots typingAfter rootsAfter ∧
      roots = [] ∧ NoParameterAccess rootsAfter.eff := by
  obtain ⟨names, roots, typingAfter, rootsAfter, world, source, checked⟩ :=
    accepted_nestedGlobal_checked nestedScalarCallsConfig (acceptedModule nestedScalarCallsConfig nestedScalarCalls_validated) 0
      nestedScalarCallsGlobal .initial [] (declaredRootTypes nestedScalarCallsModule) (fun _ => False)
      (initial_acceptedWorld nestedScalarCallsConfig nestedScalarCalls_validated) (futureGlobalsClear_initial nestedScalarCallsConfig)
      (by rfl) (Or.inl ⟨.i64, rfl⟩)
  let frame := scalarGlobalInitializerFrame nestedScalarCallsConfig 0 ExecutionState.initial.nextAct names
  have facts := nestedParameterExpression_source nestedScalarCalls_sourceForm frame.source frame.rootCursor rootsAfter roots
    (by rfl) (by rfl) (by simp [frame, scalarGlobalInitializerFrame, NoParameterAccess, Eff.accessTargets]) checked.provenance
  exact ⟨names, roots, typingAfter, rootsAfter, checked, facts⟩

theorem nestedScalarCalls_form : NestedScalarCallExpression nestedScalarCallsConfig .i64 nestedScalarCallsExpression := by
  unfold nestedScalarCallsExpression
  apply NestedScalarCallExpression.binary .add 0
  · apply NestedScalarCallExpression.call 1 0 ⟨1, "identity", [], [[]], []⟩ nestedScalarCallsHelper ⟨0, .byValue⟩
      ⟨"value", .int .i64, .immutable, 0, 0⟩ nestedScalarCallsHelperSummary (.bin .add (.read (.var 0)) (.lit .i64 3) 0)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (.binary .add 0 (.numeric (.scalar (.scalar (.localRead 0)))) (.numeric (.scalar (.scalar (.integer .i64 3)))))
    apply NestedScalarCallExpression.call 1 0 ⟨1, "identity", [], [[]], []⟩ nestedScalarCallsHelper ⟨0, .byValue⟩
      ⟨"value", .int .i64, .immutable, 0, 0⟩ nestedScalarCallsHelperSummary (.bin .add (.read (.var 0)) (.lit .i64 3) 0)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (.binary .add 0 (.numeric (.scalar (.scalar (.localRead 0)))) (.numeric (.scalar (.scalar (.integer .i64 3)))))
    exact .scalar (.numeric (.scalar (.scalar (.integer .i64 7))))
  · apply NestedScalarCallExpression.call 1 0 ⟨1, "identity", [], [[]], []⟩ nestedScalarCallsHelper ⟨0, .byValue⟩
      ⟨"value", .int .i64, .immutable, 0, 0⟩ nestedScalarCallsHelperSummary (.bin .add (.read (.var 0)) (.lit .i64 3) 0)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (.binary .add 0 (.numeric (.scalar (.scalar (.localRead 0)))) (.numeric (.scalar (.scalar (.integer .i64 3)))))
    exact .scalar (.numeric (.scalar (.scalar (.integer .i64 2))))

private def nestedScalarCallsObservation : Option Int :=
  match runModule 50 nestedScalarCallsConfig .initial with
  | .ok () state => match state.objects.lookup (.global 0) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem nestedScalarCalls_result : nestedScalarCallsObservation = some 18 := by decide +kernel

theorem nestedScalarCalls_module_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld nestedScalarCallsConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel nestedScalarCallsConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel nestedScalarCallsConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let accepted := acceptedModule nestedScalarCallsConfig nestedScalarCalls_validated
  have initial : InitialGlobalsOutcome fuel nestedScalarCallsConfig := by
    apply singleScalarInitialGlobalsOutcome fuel nestedScalarCallsConfig accepted nestedScalarCallsGlobal (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
    intro names roots typingAfter rootsAfter frame activated world source checked
    obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, result⟩ :=
      evalValue_nestedScalarCall nestedScalarCalls_form fuel accepted frame activated [] (declaredRootTypes nestedScalarCallsModule)
        (fun _ => False) [] [] world source roots typingAfter rootsAfter checked
    exact ⟨nextTypes, nextLive, nextAmbient, extend, finalWorld, clear, result⟩
  apply acceptedModuleFromGlobals_allFuel fuel nestedScalarCallsConfig accepted ⟨0, "entry", [], [], []⟩ nestedScalarCallsEntry initial (by rfl) (by rfl)
  · exact .nil
  · simp [nestedScalarCallsEntry, Block.stmts]
  · simp [nestedScalarCallsEntry, Block.stmts]
  · simp [nestedScalarCallsEntry, Block.stmts]
  · simp [nestedScalarCallsEntry, Block.stmts]
  · rfl

#print axioms nestedScalarCalls_module_allFuel
#print axioms nestedScalarCalls_result
#print axioms nestedScalarCalls_checkedRoots
#print axioms nestedScalarCalls_validated
end Goose.Proofs.ConstructionAcceptedExecution
