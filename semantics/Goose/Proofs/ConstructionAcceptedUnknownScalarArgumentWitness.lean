import Goose.Proofs.ConstructionAcceptedUnknownScalarArgument

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private def argumentWitnessSummary : SummaryAnn := .known ⟨[.param 0], [], [], [], [], [], [], [], false, false⟩
private def argumentWitnessEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none,
  .known ⟨[], [], [], [], [], [], [], [], false, false⟩⟩
private def argumentWitnessParameter : Param := ⟨0, .byValue⟩
private def argumentWitnessDescriptor : LocalVar := ⟨"value", .int .i64, .immutable, 0, 0⟩
private def argumentWitnessHelper : Impl := ⟨"helper", #[argumentWitnessParameter], #[⟨.int .i64, .register, none⟩],
  #[argumentWitnessDescriptor], .mk 0 [] (some (.read (.var 0))), argumentWitnessSummary⟩
private def argumentWitnessExpression : Expr := .bin .add (.lit .i64 3) (.lit .i64 4) 0
private def argumentWitnessGlobal : Global := ⟨"answer", .int .i64, .immutable, .call 1 [.byVal argumentWitnessExpression] 0, 0⟩
private def argumentWitnessModule : Module := ⟨#["unknown-argument.goose"], #[.int .i64], #[argumentWitnessGlobal],
  #[argumentWitnessEntry, argumentWitnessHelper], #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [], [[]], []⟩],
  0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def argumentWitnessConfig : EvalConfig := ⟨.release, argumentWitnessModule⟩

theorem argumentWitness_validated : validate argumentWitnessModule = .ok () := by cbv

theorem argumentWitness_knownSummary : ∃ summary, argumentWitnessHelper.summary = .known summary := by
  apply validated_scalar_initializer_scalarArgumentCall_known argumentWitnessConfig
    (acceptedModule argumentWitnessConfig argumentWitness_validated) 0 argumentWitnessGlobal 1 0
    ⟨1, "helper", [], [[]], []⟩ argumentWitnessHelper argumentWitnessParameter argumentWitnessDescriptor argumentWitnessExpression
    (by rfl) (Or.inl ⟨.i64, rfl⟩) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)

private def booleanArgumentDescriptor : LocalVar := ⟨"value", .bool, .immutable, 0, 0⟩
private def booleanArgumentHelper : Impl := ⟨"helper", #[argumentWitnessParameter], #[⟨.bool, .register, none⟩],
  #[booleanArgumentDescriptor], .mk 0 [] (some (.read (.var 0))), argumentWitnessSummary⟩
private def booleanArgumentExpression : Expr := .not (.bool true)
private def booleanArgumentGlobal : Global := ⟨"answer", .bool, .immutable, .call 1 [.byVal booleanArgumentExpression] 0, 0⟩
private def booleanArgumentModule : Module := ⟨#["unknown-boolean-argument.goose"], #[.bool], #[booleanArgumentGlobal],
  #[argumentWitnessEntry, booleanArgumentHelper], #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [], [[]], []⟩],
  0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def booleanArgumentConfig : EvalConfig := ⟨.release, booleanArgumentModule⟩

theorem booleanArgument_validated : validate booleanArgumentModule = .ok () := by cbv

theorem booleanArgument_knownSummary : ∃ summary, booleanArgumentHelper.summary = .known summary := by
  apply validated_scalar_initializer_scalarArgumentCall_known booleanArgumentConfig
    (acceptedModule booleanArgumentConfig booleanArgument_validated) 0 booleanArgumentGlobal 1 0
    ⟨1, "helper", [], [[]], []⟩ booleanArgumentHelper argumentWitnessParameter booleanArgumentDescriptor booleanArgumentExpression
    (by rfl) (Or.inr rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (Or.inr rfl)

#print axioms booleanArgument_validated
#print axioms booleanArgument_knownSummary
#print axioms argumentWitness_validated
#print axioms argumentWitness_knownSummary
end Goose.Proofs.ConstructionAcceptedExecution
