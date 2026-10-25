import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceCallsGlobal
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsPhysicalGlobal

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty}
  {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}
  {siteRoot : DemandNode} {siteTargets : List BlockId}

theorem globalExpressionOccurrence_call_empty {calleeId : ContextId} {arguments : List Arg} {origin : OriginId}
    (tables : SourceRootTables typingEnv env) (empty : typingEnv.vars = #[])
    (accepted : Core.validate env.mod = .ok ()) (closed : ParameterRootsClosed func)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (expressionChild : ∀ expression, Arg.byVal expression ∈ arguments → ∀ state provenance,
      GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
        expression state provenance)
    (placeChild : ∀ mutability place, Arg.byRef mutability place ∈ arguments → ∀ state provenance,
      GlobalPlaceOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
        place state provenance) :
    GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
      (.call calleeId arguments origin) initial upper := by
  exact globalExpressionOccurrence_call tables accepted closed validity bounded
    (fun argument member => typedEmptyPhysicalArgumentOccurrence tables empty argument
      (fun expression same => expressionChild expression (same ▸ member))
      (fun mutability place same => placeChild mutability place (same ▸ member)))

#print axioms globalExpressionOccurrence_call_empty

end Goose.Lower.Validation.ReplacementContentFlowSource
