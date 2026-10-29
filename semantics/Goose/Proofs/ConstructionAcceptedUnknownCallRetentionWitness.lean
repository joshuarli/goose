import Goose.Proofs.ConstructionAcceptedUnknownCallRetention

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private def callRetentionSummary : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def callRetentionEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, callRetentionSummary⟩
private def callRetentionHelper : Impl := ⟨"helper", #[], #[⟨.int .i64, .register, none⟩], #[],
  .mk 0 [] (some (.lit .i64 3)), callRetentionSummary⟩
private def callRetentionParameter : Param := ⟨0, .byValue⟩
private def callRetentionDescriptor : LocalVar := ⟨"value", .int .i64, .immutable, 0, 0⟩
private def callRetentionOther : Impl := ⟨"other", #[callRetentionParameter], #[⟨.int .i64, .register, none⟩], #[callRetentionDescriptor],
  .mk 0 [] (some (.read (.var 0))), .known ⟨[.param 0], [], [], [], [], [], [], [], false, false⟩⟩
private def callRetentionGlobal : Global := ⟨"answer", .int .i64, .immutable,
  .bin .add (.call 1 [] 0) (.un .neg (.call 2 [.byVal (.call 1 [] 0)] 0) 0) 0, 0⟩
private def callRetentionModule : Module := ⟨#["unknown-call-retention.goose"], #[.int .i64], #[callRetentionGlobal],
  #[callRetentionEntry, callRetentionHelper, callRetentionOther],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [], [[]], []⟩, ⟨2, "other", [], [[]], []⟩],
  0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def callRetentionConfig : EvalConfig := ⟨.release, callRetentionModule⟩

theorem callRetention_validated : validate callRetentionModule = .ok () := by cbv

theorem callRetention_knownSummary : ∃ summary, callRetentionHelper.summary = .known summary := by
  apply validated_scalar_initializer_binaryLeftCalls_known callRetentionConfig
    (acceptedModule callRetentionConfig callRetention_validated) 0 callRetentionGlobal 1 0
    ⟨1, "helper", [], [[]], []⟩ callRetentionHelper .add (.call 1 [] 0) (.un .neg (.call 2 [.byVal (.call 1 [] 0)] 0) 0) 0
    (by rfl) (Or.inl ⟨.i64, rfl⟩) (by rfl) .call
  · exact .unary .neg 0 (.scalarCall 2 0 ⟨2, "other", [], [[]], []⟩ callRetentionOther
      callRetentionParameter callRetentionDescriptor rfl rfl rfl rfl (Or.inl ⟨.i64, rfl⟩)
      (.call 1 0 ⟨1, "helper", [], [[]], []⟩ callRetentionHelper rfl rfl rfl))
  · rfl
  · rfl
  · rfl

#print axioms callRetention_validated
#print axioms callRetention_knownSummary
end Goose.Proofs.ConstructionAcceptedExecution
