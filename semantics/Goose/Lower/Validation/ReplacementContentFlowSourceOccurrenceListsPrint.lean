import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceListsPrintContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceListsPrintGlobal

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat}
  {siteRoot anchor : DemandNode} {siteTargets : List BlockId}

theorem typedPrintArgumentsOccurrence (arguments : List PrintArg)
    (step : ∀ expression, .expr expression ∈ arguments → ∀ state provenance,
      ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets
        expression state provenance) :
    ∀ initial upper, PrintArgumentsOccurrenceReplayAt typingEnv env results vt target scopeCount
      siteRoot siteTargets anchor arguments initial upper := by
  exact typedGlobalPrintArgumentsOccurrence arguments step

end Goose.Lower.Validation.ReplacementContentFlowSource
