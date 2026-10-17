import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsGlobal

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat}
  {siteRoot anchor : DemandNode} {siteTargets : List BlockId}

theorem typedArgumentOccurrence (argument : Arg)
    (expressionChild : ∀ expression, argument = .byVal expression → ∀ state provenance,
      ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets
        expression state provenance)
    (placeChild : ∀ mutability place, argument = .byRef mutability place → ∀ state provenance,
      PlaceOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets
        place state provenance) :
    ∀ initial upper, ArgumentOccurrenceReplayAt typingEnv env results vt target scopeCount
      siteRoot siteTargets anchor argument initial upper := by
  exact typedGlobalArgumentOccurrence argument expressionChild placeChild

end Goose.Lower.Validation.ReplacementContentFlowSource
