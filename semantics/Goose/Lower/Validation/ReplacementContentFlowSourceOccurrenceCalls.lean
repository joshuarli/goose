import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceCallsGlobal
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsPhysical

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}
  {siteRoot : DemandNode} {siteTargets : List BlockId}

theorem expressionOccurrence_call {context : ContextId} {calleeId : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (expressionChild : ∀ expression, Arg.byVal expression ∈ arguments → ∀ state provenance,
      ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets expression state provenance)
    (placeChild : ∀ mutability place, Arg.byRef mutability place ∈ arguments → ∀ state provenance,
      PlaceOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets place state provenance) :
    ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets
      (.call calleeId arguments origin) initial upper := by
  exact globalExpressionOccurrence_call source.tables source.accepted source.parameters validity bounded
    (fun argument member => typedContextPhysicalArgumentOccurrence source argument
      (fun expression same => expressionChild expression (same ▸ member))
      (fun mutability place same => placeChild mutability place (same ▸ member)))

end Goose.Lower.Validation.ReplacementContentFlowSource
