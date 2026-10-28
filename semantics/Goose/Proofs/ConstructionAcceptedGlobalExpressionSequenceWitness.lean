import Goose.Proofs.ConstructionAcceptedGlobalExpressionSequence

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private def globalExpressionSequenceEntry : Impl :=
  ⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩

private def globalExpressionSequenceModule : Module :=
  ⟨#["branch.goose"], #[.int .i64],
    #[⟨"source", .int .i64, .immutable, .lit .i64 1, 0⟩,
      ⟨"number", .int .i64, .immutable,
        .ifE (.bool true) (.mk 0 [.expr (.bin .add (.read (.global 0)) (.lit .i64 2) 0) 0]
          (some (.bin .add (.read (.global 0)) (.lit .i64 2) 0))) (.mk 1 [] (some (.lit .i64 4))) 0, 0⟩],
    #[globalExpressionSequenceEntry], #[⟨0, "entry", [], [], []⟩], 0, #[⟨0, 1, "assign"⟩], #[], #[]⟩

private def globalExpressionSequenceConfig : EvalConfig := ⟨.release, globalExpressionSequenceModule⟩

theorem globalExpressionSequence_validated : validate globalExpressionSequenceModule = .ok () := by cbv

private def globalExpressionSequenceObservation : Option Int :=
  match runModule 100 globalExpressionSequenceConfig .initial with
  | .ok () state => match state.objects.lookup (.global 1) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem globalExpressionSequence_result : globalExpressionSequenceObservation = some 3 := by decide +kernel

#print axioms globalExpressionSequence_validated
#print axioms globalExpressionSequence_result
end Goose.Proofs.ConstructionAcceptedExecution
