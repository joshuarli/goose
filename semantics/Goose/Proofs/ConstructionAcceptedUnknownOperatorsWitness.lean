import Goose.Proofs.ConstructionAcceptedUnknownOperators

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private def operatorWitnessSummary : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def operatorWitnessEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, operatorWitnessSummary⟩
private def operatorWitnessHelper : Impl := ⟨"helper", #[], #[⟨.int .i64, .register, none⟩], #[],
  .mk 0 [] (some (.lit .i64 3)), operatorWitnessSummary⟩
private def operatorWitnessGlobal : Global := ⟨"answer", .int .i64, .immutable,
  .bin .add (.lit .i64 1) (.un .neg (.call 1 [] 0) 0) 0, 0⟩
private def operatorWitnessModule : Module := ⟨#["unknown-operator.goose"], #[.int .i64], #[operatorWitnessGlobal],
  #[operatorWitnessEntry, operatorWitnessHelper], #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [], [[]], []⟩],
  0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def operatorWitnessConfig : EvalConfig := ⟨.release, operatorWitnessModule⟩

theorem operatorWitness_validated : validate operatorWitnessModule = .ok () := by cbv

theorem operatorWitness_knownSummary : ∃ summary, operatorWitnessHelper.summary = .known summary := by
  apply validated_scalar_initializer_operatorWrappedZeroCall_known operatorWitnessConfig
    (acceptedModule operatorWitnessConfig operatorWitness_validated) 0 operatorWitnessGlobal 1 0
    ⟨1, "helper", [], [[]], []⟩ operatorWitnessHelper (by rfl) (Or.inl ⟨.i64, rfl⟩)
  · exact .binaryRight .add (.lit .i64 1) 0 (.unary .neg 0 .call)
  · rfl
  · rfl
  · rfl

#print axioms operatorWitness_validated
#print axioms operatorWitness_knownSummary
end Goose.Proofs.ConstructionAcceptedExecution
