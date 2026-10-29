import Goose.Proofs.ConstructionAcceptedUnknownOperators

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private def wrappedArgumentsSummary : SummaryAnn := .known ⟨[.param 0], [], [], [], [], [], [], [], false, false⟩
private def wrappedArgumentsEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none,
  .known ⟨[], [], [], [], [], [], [], [], false, false⟩⟩
private def wrappedArgumentsFirst : Param := ⟨0, .byValue⟩
private def wrappedArgumentsSecond : Param := ⟨1, .byValue⟩
private def wrappedArgumentsFirstDescriptor : LocalVar := ⟨"number", .int .i64, .immutable, 0, 0⟩
private def wrappedArgumentsSecondDescriptor : LocalVar := ⟨"condition", .bool, .immutable, 0, 0⟩
private def wrappedArgumentsHelper : Impl := ⟨"helper", #[wrappedArgumentsFirst, wrappedArgumentsSecond], #[⟨.int .i64, .register, none⟩],
  #[wrappedArgumentsFirstDescriptor, wrappedArgumentsSecondDescriptor], .mk 0 [] (some (.read (.var 0))), wrappedArgumentsSummary⟩
private def wrappedArgumentsNumber : Expr := .bin .add (.lit .i64 3) (.lit .i64 4) 0
private def wrappedArgumentsCondition : Expr := .not (.bool true)
private def wrappedArgumentsGlobal : Global := ⟨"answer", .int .i64, .immutable,
  .bin .add (.lit .i64 1) (.call 1 [.byVal wrappedArgumentsNumber, .byVal wrappedArgumentsCondition] 0) 0, 0⟩
private def wrappedArgumentsModule : Module := ⟨#["unknown-wrapped-arguments.goose"], #[.int .i64, .bool], #[wrappedArgumentsGlobal],
  #[wrappedArgumentsEntry, wrappedArgumentsHelper], #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [], [[]], []⟩],
  0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def wrappedArgumentsConfig : EvalConfig := ⟨.release, wrappedArgumentsModule⟩

theorem wrappedArguments_validated : validate wrappedArgumentsModule = .ok () := by cbv

theorem wrappedArguments_knownSummary : ∃ summary, wrappedArgumentsHelper.summary = .known summary := by
  apply validated_scalar_initializer_operatorWrappedCall_known wrappedArgumentsConfig
    (acceptedModule wrappedArgumentsConfig wrappedArguments_validated) 0 wrappedArgumentsGlobal 1 0
    [.byVal wrappedArgumentsNumber, .byVal wrappedArgumentsCondition]
    ⟨1, "helper", [], [[]], []⟩ wrappedArgumentsHelper (by rfl) (Or.inl ⟨.i64, rfl⟩)
  · exact .binaryRight .add (.lit .i64 1) 0 .call
  · rfl
  · rfl

#print axioms wrappedArguments_validated
#print axioms wrappedArguments_knownSummary
end Goose.Proofs.ConstructionAcceptedExecution
