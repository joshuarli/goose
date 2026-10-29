import Goose.Proofs.ConstructionAcceptedUnknownRetention

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private def retentionWitnessSummary : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def retentionWitnessEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, retentionWitnessSummary⟩
private def retentionWitnessHelper : Impl := ⟨"helper", #[], #[⟨.int .i64, .register, none⟩], #[],
  .mk 0 [] (some (.lit .i64 3)), retentionWitnessSummary⟩
private def retentionWitnessGlobal : Global := ⟨"answer", .int .i64, .immutable,
  .bin .add (.call 1 [] 0) (.bin .add (.un .neg (.lit .i64 2) 0) (.lit .i64 1) 0) 0, 0⟩
private def retentionWitnessModule : Module := ⟨#["unknown-retention.goose"], #[.int .i64], #[retentionWitnessGlobal],
  #[retentionWitnessEntry, retentionWitnessHelper], #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [], [[]], []⟩],
  0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def retentionWitnessConfig : EvalConfig := ⟨.release, retentionWitnessModule⟩

theorem retentionWitness_validated : validate retentionWitnessModule = .ok () := by cbv

theorem retentionWitness_knownSummary : ∃ summary, retentionWitnessHelper.summary = .known summary := by
  apply validated_scalar_initializer_binaryLeftScalar_known retentionWitnessConfig
    (acceptedModule retentionWitnessConfig retentionWitness_validated) 0 retentionWitnessGlobal 1 0
    ⟨1, "helper", [], [[]], []⟩ retentionWitnessHelper .add (.call 1 [] 0)
    (.bin .add (.un .neg (.lit .i64 2) 0) (.lit .i64 1) 0) 0
    (by rfl) (Or.inl ⟨.i64, rfl⟩) (by rfl) .call
  · exact .binary .add 0 (.unary .neg 0 (.numeric (.scalar (.scalar (.integer .i64 2)))))
      (.numeric (.scalar (.scalar (.integer .i64 1))))
  · rfl
  · rfl
  · rfl

#print axioms retentionWitness_validated
#print axioms retentionWitness_knownSummary
end Goose.Proofs.ConstructionAcceptedExecution
