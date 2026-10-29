import Goose.Proofs.ConstructionAcceptedUnknownLeftOperator

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private def leftOperatorWitnessSummary : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def leftOperatorWitnessEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, leftOperatorWitnessSummary⟩
private def leftOperatorWitnessHelper : Impl := ⟨"helper", #[], #[⟨.int .i64, .register, none⟩], #[],
  .mk 0 [] (some (.lit .i64 3)), leftOperatorWitnessSummary⟩
private def leftOperatorWitnessGlobal : Global := ⟨"answer", .int .i64, .immutable,
  .bin .add (.call 1 [] 0) (.lit .i64 1) 0, 0⟩
private def leftOperatorWitnessModule : Module := ⟨#["unknown-left-operator.goose"], #[.int .i64], #[leftOperatorWitnessGlobal],
  #[leftOperatorWitnessEntry, leftOperatorWitnessHelper], #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [], [[]], []⟩],
  0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def leftOperatorWitnessConfig : EvalConfig := ⟨.release, leftOperatorWitnessModule⟩

theorem leftOperatorWitness_validated : validate leftOperatorWitnessModule = .ok () := by cbv

theorem leftOperatorWitness_knownSummary : ∃ summary, leftOperatorWitnessHelper.summary = .known summary := by
  apply validated_scalar_initializer_binaryLeft_known leftOperatorWitnessConfig
    (acceptedModule leftOperatorWitnessConfig leftOperatorWitness_validated) 0 leftOperatorWitnessGlobal 1 0
    ⟨1, "helper", [], [[]], []⟩ leftOperatorWitnessHelper .add (.call 1 [] 0) (.lit .i64 1) 0
    (by rfl) (Or.inl ⟨.i64, rfl⟩) (by rfl) .call (.integer .i64 1) (by rfl) (by rfl) (by rfl)

#print axioms leftOperatorWitness_validated
#print axioms leftOperatorWitness_knownSummary
end Goose.Proofs.ConstructionAcceptedExecution
