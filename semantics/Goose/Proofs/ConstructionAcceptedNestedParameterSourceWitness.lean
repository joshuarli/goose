import Goose.Proofs.ConstructionAcceptedNestedParameterSource
import Goose.Proofs.ConstructionAcceptedNestedGlobal
import Goose.Proofs.ConstructionAcceptedSingleScalarGlobal

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

private def nestedParameterEntrySummary : Summary := ⟨[], [], [], [], [], [], [], [], false, false⟩
private def nestedParameterHelperSummary : Summary := ⟨[.param 0], [], [], [], [], [], [], [], false, false⟩
private def nestedParameterEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .known nestedParameterEntrySummary⟩
private def nestedParameterHelper : Impl := ⟨"identity", #[⟨0, .byValue⟩], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩], .mk 0 [] (some (.read (.var 0))), .known nestedParameterHelperSummary⟩
private def nestedParameterExpression : Expr := .call 1 [.byVal (.call 1 [.byVal (.lit .i64 7)] 0)] 0
private def nestedParameterGlobal : Global := ⟨"answer", .int .i64, .immutable, nestedParameterExpression, 0⟩
private def nestedParameterModule : Module := ⟨#["nested-parameter-source.goose"], #[.int .i64], #[nestedParameterGlobal],
  #[nestedParameterEntry, nestedParameterHelper], #[⟨0, "entry", [], [], []⟩, ⟨1, "identity", [], [[]], []⟩], 0,
  #[⟨0, 1, "call"⟩], #[], #[]⟩
private def nestedParameterConfig : EvalConfig := ⟨.release, nestedParameterModule⟩

theorem nestedParameter_validated : validate nestedParameterModule = .ok () := by cbv

theorem nestedParameter_sourceForm : NestedParameterExpression nestedParameterConfig .i64 initImpl
    nestedParameterExpression := by
  unfold nestedParameterExpression
  apply NestedParameterExpression.call 1 0 ⟨1, "identity", [], [[]], []⟩ nestedParameterHelper ⟨0, .byValue⟩ nestedParameterHelperSummary
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  apply NestedParameterExpression.call 1 0 ⟨1, "identity", [], [[]], []⟩ nestedParameterHelper ⟨0, .byValue⟩ nestedParameterHelperSummary
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  exact .literal 7

theorem nestedParameter_checkedRoots :
    ∃ names roots typingAfter rootsAfter,
      let frame := scalarGlobalInitializerFrame nestedParameterConfig 0 ExecutionState.initial.nextAct names
      CheckedValue frame nestedParameterExpression (.int .i64) roots typingAfter rootsAfter ∧
      roots = [] ∧ NoParameterAccess rootsAfter.eff := by
  obtain ⟨names, roots, typingAfter, rootsAfter, world, source, checked⟩ :=
    accepted_nestedGlobal_checked nestedParameterConfig (acceptedModule nestedParameterConfig nestedParameter_validated) 0
      nestedParameterGlobal .initial [] (declaredRootTypes nestedParameterModule) (fun _ => False)
      (initial_acceptedWorld nestedParameterConfig nestedParameter_validated) (futureGlobalsClear_initial nestedParameterConfig)
      (by rfl) (Or.inl ⟨.i64, rfl⟩)
  let frame := scalarGlobalInitializerFrame nestedParameterConfig 0 ExecutionState.initial.nextAct names
  have facts := nestedParameterExpression_source nestedParameter_sourceForm frame.source frame.rootCursor rootsAfter roots
    (by rfl) (by rfl) (by simp [frame, scalarGlobalInitializerFrame, NoParameterAccess, Eff.accessTargets]) checked.provenance
  exact ⟨names, roots, typingAfter, rootsAfter, checked, facts⟩

#print axioms nestedParameter_checkedRoots
#print axioms nestedParameter_validated
end Goose.Proofs.ConstructionAcceptedExecution
