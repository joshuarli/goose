import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceListsGlobalContracts

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation

abbrev ExpressionsOccurrenceReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat)
    (siteRoot : DemandNode) (siteTargets : List BlockId) (anchor : DemandNode)
    (expressions : List Expr) (initial : LS) (upper : Prov) : Prop :=
  GlobalExpressionsOccurrenceReplayAt typingEnv env results vt
    (lowerContextAt env.mod env.ctx env.impl) env.impl.results.toList
    (typedContextSlotUpper env.mod env.ctx env.impl) target scopeCount
    siteRoot siteTargets anchor expressions initial upper

end Goose.Lower.Validation.ReplacementContentFlowSource
