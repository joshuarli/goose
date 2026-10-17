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

theorem emptyParameterResult_gir_rejected :
    GIR.validate (lower emptyParameterResult) =
      .error ⟨.v050, "function receiver result 0 root info omits a root returned by the body"⟩ := by
  cbv

end Goose.Lower.Validation.SummaryPreservation
