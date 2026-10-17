import Goose.Lower.Validation.Checks

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core

set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

def readonlySliceCoercion : Module :=
  let receiver : Impl :=
    { name := "receiver", params := #[⟨0, .byValue⟩], results := #[],
      vars := #[⟨"source", .slice .mutable (.int .i64), .immutable, 0, 0⟩,
        ⟨"borrow", .slice .readOnly (.int .i64), .immutable, 0, 0⟩],
      body := .mk 0 [.letS 1 (.read (.var 0)) 0] none,
      summary := .known ⟨[], [], [], [], [], false, false⟩ }
  { files := #["readonly-slice-coercion.goose"], types := #[], globals := #[],
    impls := #[Checks.emptyEntry, receiver],
    contexts := #[⟨0, "main", [], [], []⟩,
      ⟨1, "receiver", [(0, [.param 0]), (1, [.param 0])], [], []⟩],
    entry := 0, origins := #[⟨0, 1, "expr"⟩] }

theorem readonlySliceCoercion_core_accepted : Core.validate readonlySliceCoercion = .ok () := by
  cbv

theorem readonlySliceCoercion_gir_rejected :
    (match GIR.validate (lower readonlySliceCoercion) with
    | .error rejection => rejection.code == .v050
    | .ok _ => false) = true := by
  cbv

end Goose.Lower.Validation.SummaryPreservation
