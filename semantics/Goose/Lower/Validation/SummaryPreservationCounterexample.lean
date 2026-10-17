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

def genericParameterContext : Module :=
  let base := Checks.specializedParameterSummary
  { base with contexts := base.contexts.modify 1 fun ctx =>
      { ctx with varRoots := [(0, [.param 0])] } }

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem genericParameterContext_core_accepted : validate genericParameterContext = .ok () := by
  cbv

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem genericParameterContext_gir_rejected :
    Goose.GIR.validate (lower genericParameterContext) =
      .error ⟨.v050, "function receiver parameter 0 root info omits a root passed at a call site"⟩ := by
  cbv

end Goose.Lower.Validation.SummaryPreservation
