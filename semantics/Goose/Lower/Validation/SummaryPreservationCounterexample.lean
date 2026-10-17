import Goose.Lower.Validation.Checks

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core

def sharedCalleeContexts : Module :=
  let base := Checks.specializedParameterSummary
  { base with
    globals := base.globals.push ⟨"other", .int .i64, .mutable, .lit .i64 2, 0⟩
    contexts := base.contexts.push ⟨1, "receiver-other", [(0, [.global 1])], [], []⟩ }

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem sharedCalleeContexts_core_accepted : validate sharedCalleeContexts = .ok () := by
  cbv

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem sharedCalleeContexts_gir_rejected :
    Goose.GIR.validate (lower sharedCalleeContexts) =
      .error ⟨.v050, "function main: main reads global 1, which its summary omits"⟩ := by
  cbv

end Goose.Lower.Validation.SummaryPreservation
