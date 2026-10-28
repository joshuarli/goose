import Goose.Proofs.ConstructionAcceptedGlobalBranchExpression

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private def globalBranchExpressionEntry : Impl :=
  ⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩

private def globalBranchExpressionModule : Module :=
  ⟨#["branch.goose"], #[.int .i64],
    #[⟨"number", .int .i64, .immutable,
        .ifE (.bool true) (.mk 0 [.expr (.lit .i64 7) 0] (some (.lit .i64 3))) (.mk 1 [] (some (.lit .i64 4))) 0, 0⟩],
    #[globalBranchExpressionEntry], #[⟨0, "entry", [], [], []⟩], 0, #[⟨0, 1, "assign"⟩], #[], #[]⟩

private def globalBranchExpressionConfig : EvalConfig := ⟨.release, globalBranchExpressionModule⟩

theorem globalBranchExpression_validated : validate globalBranchExpressionModule = .ok () := by cbv

private def globalBranchExpressionObservation : Option Int :=
  match runModule 100 globalBranchExpressionConfig .initial with
  | .ok () state => match state.objects.lookup (.global 0) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem globalBranchExpression_result : globalBranchExpressionObservation = some 3 := by decide +kernel

#print axioms globalBranchExpression_validated
#print axioms globalBranchExpression_result
end Goose.Proofs.ConstructionAcceptedExecution
