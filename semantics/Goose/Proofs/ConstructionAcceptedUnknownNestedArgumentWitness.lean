import Goose.Proofs.ConstructionAcceptedUnknownCallRetention

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private def nestedArgumentSummary : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def nestedArgumentEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, nestedArgumentSummary⟩
private def nestedArgumentHelper : Impl := ⟨"helper", #[], #[⟨.int .i64, .register, none⟩], #[],
  .mk 0 [] (some (.lit .i64 3)), nestedArgumentSummary⟩
private def nestedArgumentParameter : Param := ⟨0, .byValue⟩
private def nestedArgumentDescriptor : LocalVar := ⟨"value", .int .i64, .immutable, 0, 0⟩
private def nestedArgumentOther : Impl := ⟨"other", #[nestedArgumentParameter], #[⟨.int .i64, .register, none⟩], #[nestedArgumentDescriptor],
  .mk 0 [] (some (.read (.var 0))), .known ⟨[.param 0], [], [], [], [], [], [], [], false, false⟩⟩
private def nestedArgumentGlobal : Global := ⟨"answer", .int .i64, .immutable,
  .call 2 [.byVal (.un .neg (.call 2 [.byVal (.un .neg (.call 1 [] 0) 0)] 0) 0)] 0, 0⟩
private def nestedArgumentModule : Module := ⟨#["unknown-nested-argument.goose"], #[.int .i64], #[nestedArgumentGlobal],
  #[nestedArgumentEntry, nestedArgumentHelper, nestedArgumentOther],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [], [[]], []⟩, ⟨2, "other", [], [[]], []⟩],
  0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def nestedArgumentConfig : EvalConfig := ⟨.release, nestedArgumentModule⟩

theorem nestedArgument_validated : validate nestedArgumentModule = .ok () := by cbv

theorem nestedArgument_knownSummary : ∃ summary, nestedArgumentHelper.summary = .known summary := by
  apply validated_scalar_initializer_nestedCallPath_known nestedArgumentConfig
    (acceptedModule nestedArgumentConfig nestedArgument_validated) 0 nestedArgumentGlobal 1 0 []
    ⟨1, "helper", [], [[]], []⟩ nestedArgumentHelper (by rfl) (Or.inl ⟨.i64, rfl⟩)
  · exact .scalarArgument 2 0 ⟨2, "other", [], [[]], []⟩ nestedArgumentOther nestedArgumentParameter nestedArgumentDescriptor
      rfl rfl rfl rfl (Or.inl ⟨.i64, rfl⟩)
      (.unary .neg 0 (.scalarArgument 2 0 ⟨2, "other", [], [[]], []⟩ nestedArgumentOther nestedArgumentParameter nestedArgumentDescriptor
        rfl rfl rfl rfl (Or.inl ⟨.i64, rfl⟩) (.unary .neg 0 .call)))
  · rfl
  · rfl

#print axioms nestedArgument_validated
#print axioms nestedArgument_knownSummary
end Goose.Proofs.ConstructionAcceptedExecution
