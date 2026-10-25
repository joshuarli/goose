import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsGlobalLists

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat}
  {siteRoot anchor : DemandNode} {siteTargets : List BlockId}

theorem typedArgumentsOccurrence (arguments : List Arg)
    (step : ∀ argument ∈ arguments, ∀ state provenance,
      ArgumentOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets
        anchor argument state provenance) :
    ∀ initial upper, ArgumentsOccurrenceReplayAt typingEnv env results vt target scopeCount
      siteRoot siteTargets anchor arguments initial upper := by
  exact typedGlobalArgumentsOccurrence arguments step

end Goose.Lower.Validation.ReplacementContentFlowSource
