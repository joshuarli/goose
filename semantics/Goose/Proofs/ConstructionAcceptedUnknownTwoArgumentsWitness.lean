import Goose.Proofs.ConstructionAcceptedUnknownAnyArguments

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private def twoArgumentSummary : SummaryAnn := .known ⟨[.param 0], [], [], [], [], [], [], [], false, false⟩
private def twoArgumentEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none,
  .known ⟨[], [], [], [], [], [], [], [], false, false⟩⟩
private def twoArgumentFirst : Param := ⟨0, .byValue⟩
private def twoArgumentSecond : Param := ⟨1, .byValue⟩
private def twoArgumentFirstDescriptor : LocalVar := ⟨"number", .int .i64, .immutable, 0, 0⟩
private def twoArgumentSecondDescriptor : LocalVar := ⟨"condition", .bool, .immutable, 0, 0⟩
private def twoArgumentHelper : Impl := ⟨"helper", #[twoArgumentFirst, twoArgumentSecond], #[⟨.int .i64, .register, none⟩],
  #[twoArgumentFirstDescriptor, twoArgumentSecondDescriptor], .mk 0 [] (some (.read (.var 0))), twoArgumentSummary⟩
private def twoArgumentNumber : Expr := .bin .add (.lit .i64 3) (.lit .i64 4) 0
private def twoArgumentCondition : Expr := .not (.bool true)
private def twoArgumentGlobal : Global := ⟨"answer", .int .i64, .immutable,
  .call 1 [.byVal twoArgumentNumber, .byVal twoArgumentCondition] 0, 0⟩
private def twoArgumentModule : Module := ⟨#["unknown-two-arguments.goose"], #[.int .i64, .bool], #[twoArgumentGlobal],
  #[twoArgumentEntry, twoArgumentHelper], #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [], [[]], []⟩],
  0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def twoArgumentConfig : EvalConfig := ⟨.release, twoArgumentModule⟩

theorem twoArgument_validated : validate twoArgumentModule = .ok () := by cbv

theorem twoArgument_knownSummary : ∃ summary, twoArgumentHelper.summary = .known summary := by
  exact validated_scalar_initializer_anyCall_known twoArgumentConfig (acceptedModule twoArgumentConfig twoArgument_validated)
    0 twoArgumentGlobal 1 0 ⟨1, "helper", [], [[]], []⟩ twoArgumentHelper
    [.byVal twoArgumentNumber, .byVal twoArgumentCondition] (by rfl) (Or.inl ⟨.i64, rfl⟩) (by rfl) (by rfl) (by rfl)

#print axioms twoArgument_validated
#print axioms twoArgument_knownSummary
end Goose.Proofs.ConstructionAcceptedExecution
