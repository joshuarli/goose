import Goose.Lower.Validation.SummaryPreservationCallAnnotationChecks

namespace Goose.Lower.Validation.ReplacementParameterAnnotationChecks

open Goose.Core Goose.GIR
open SummaryPreservation.CallAnnotationChecks

private def fixedGlobalOnly : Core.Module :=
  { specializedCallerContent with
    contexts := specializedCallerContent.contexts.modify 2 fun context =>
      { context with varRoots := [(1, [.global 1])] } }

#guard match Core.validate fixedGlobalOnly with
  | .error rejection => rejection.rule == .call
  | _ => false

#guard match GIR.validate (lower fixedGlobalOnly) with
  | .error rejection => rejection.code == .v050
  | _ => false

end Goose.Lower.Validation.ReplacementParameterAnnotationChecks
