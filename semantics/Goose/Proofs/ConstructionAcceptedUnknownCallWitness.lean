import Goose.Proofs.ConstructionAcceptedUnknownCall

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private def unknownWitnessSummary : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def unknownWitnessEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, unknownWitnessSummary⟩
private def unknownWitnessHelper : Impl := ⟨"helper", #[], #[⟨.bool, .register, none⟩], #[],
  .mk 0 [] (some (.bool true)), unknownWitnessSummary⟩
private def unknownWitnessGlobal : Global := ⟨"answer", .bool, .immutable, .not (.not (.call 1 [] 0)), 0⟩
private def unknownWitnessModule : Module := ⟨#["unknown-call.goose"], #[.bool], #[unknownWitnessGlobal],
  #[unknownWitnessEntry, unknownWitnessHelper], #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [], [[]], []⟩],
  0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def unknownWitnessConfig : EvalConfig := ⟨.release, unknownWitnessModule⟩

theorem unknownWitness_validated : validate unknownWitnessModule = .ok () := by cbv

theorem unknownWitness_knownSummary : ∃ summary, unknownWitnessHelper.summary = .known summary := by
  apply validated_scalar_initializer_notWrappedZeroCall_known unknownWitnessConfig
    (acceptedModule unknownWitnessConfig unknownWitness_validated) 0 unknownWitnessGlobal 1 0
    ⟨1, "helper", [], [[]], []⟩ unknownWitnessHelper (by rfl) (Or.inr rfl)
  · exact .not (.not .call)
  · rfl
  · rfl
  · rfl

#print axioms unknownWitness_validated
#print axioms unknownWitness_knownSummary
end Goose.Proofs.ConstructionAcceptedExecution
