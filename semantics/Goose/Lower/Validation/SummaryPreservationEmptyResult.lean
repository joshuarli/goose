import Goose.Lower.Validation.Checks

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core

set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

def emptyParameterResult : Module :=
  let reference := Ty.ref .readOnly (.int .i64)
  let receiver : Impl :=
    { name := "receiver", params := #[⟨0, .byRef⟩], results := #[reference],
      vars := #[⟨"p", reference, .immutable, 0, 0⟩],
      body := .mk 0 [] (some (.read (.var 0))), summary := .known ⟨[], [], [], [], [], false, false⟩ }
  { files := #["empty-parameter-result.goose"], types := #[], globals := #[],
    impls := #[Checks.emptyEntry, receiver],
    contexts := #[⟨0, "main", [], [], []⟩, ⟨1, "receiver", [(0, [])], [[]], []⟩],
    entry := 0, origins := #[⟨0, 1, "expr"⟩] }

theorem emptyParameterResult_core_accepted :
    Core.validate emptyParameterResult = .ok () := by
  cbv

attribute [local cbv_opaque] Goose.GIR.replacementContentFlow

theorem emptyParameterResult_gir_accepted :
    GIR.validate (lower emptyParameterResult) = .ok () := by
  cbv


def partialParameterResult : Module :=
  { emptyParameterResult with
    globals := #[⟨"first", .int .i64, .mutable, .lit .i64 0, 0⟩,
      ⟨"second", .int .i64, .mutable, .lit .i64 1, 0⟩],
    contexts := emptyParameterResult.contexts.modify 1 fun ctx =>
      { ctx with varRoots := [(0, [.global 0, .global 1])], resultRoots := [[.global 0]] } }

theorem partialParameterResult_core_rejected :
    (match Core.validate partialParameterResult with
    | .error rejection => rejection.rule == .result
    | .ok _ => false) = true := by
  cbv

theorem partialParameterResult_gir_rejected :
    GIR.validate (lower partialParameterResult) =
      .error ⟨.v050, "declared regions: receiver root info does not bound a stored, returned, or passed region"⟩ := by
  cbv

end Goose.Lower.Validation.SummaryPreservation
