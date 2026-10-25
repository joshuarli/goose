import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceListsPrintGlobalContracts

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation

abbrev PrintArgumentsOccurrenceReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat)
    (siteRoot : DemandNode) (siteTargets : List BlockId) (anchor : DemandNode)
    (arguments : List PrintArg) (initial : LS) (upper : Prov) : Prop :=
  GlobalPrintArgumentsOccurrenceReplayAt typingEnv env results vt
    (lowerContextAt env.mod env.ctx env.impl) env.impl.results.toList
    (typedContextSlotUpper env.mod env.ctx env.impl) target scopeCount
    siteRoot siteTargets anchor arguments initial upper

end Goose.Lower.Validation.ReplacementContentFlowSource
