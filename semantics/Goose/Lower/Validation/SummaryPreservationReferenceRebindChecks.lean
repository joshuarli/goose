import Goose.Lower.Validation.Checks

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core

set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

def referenceVariableRebind : Module :=
  let receiver : Impl :=
    { name := "reference_parameter", params := #[⟨0, .byRef⟩], results := #[],
      vars := #[⟨"pointer", .ref .mutable (.int .i64), .mutable, 0, 0⟩],
      body := .mk 0 [.rebind 0 (.ref .mutable (.global 0)) 0] none,
      summary := .known ⟨[], [], [], [], [.param 0], false, false⟩ }
  { files := #["reference-rebind.goose"], types := #[],
    globals := #[⟨"value", .int .i64, .mutable, .lit .i64 0, 0⟩],
    impls := #[Checks.emptyEntry, receiver],
    contexts := #[⟨0, "main", [], [], []⟩,
      ⟨1, "reference_parameter", [(0, [.global 0])], [], []⟩],
    entry := 0, origins := #[⟨0, 1, "rebind"⟩] }

def undeclaredReferenceVariableRebind : Module :=
  { referenceVariableRebind with
    impls := referenceVariableRebind.impls.modify 1 fun impl =>
      { impl with summary := .known ⟨[], [], [], [], [], false, false⟩ } }

theorem referenceVariableRebind_core_accepted : Core.validate referenceVariableRebind = .ok () := by
  cbv

attribute [local cbv_opaque] Goose.GIR.replacementContentFlow

theorem referenceVariableRebind_gir_accepted : GIR.validate (lower referenceVariableRebind) = .ok () := by
  cbv

theorem undeclaredReferenceVariableRebind_core_rejected :
    (match Core.validate undeclaredReferenceVariableRebind with
    | .error _ => true
    | .ok _ => false) = true := by
  cbv

theorem undeclaredReferenceVariableRebind_gir_rejected :
    (match GIR.validate (lower undeclaredReferenceVariableRebind) with
    | .error rejection => rejection.code == .v050
    | .ok _ => false) = true := by
  cbv

end Goose.Lower.Validation.SummaryPreservation
