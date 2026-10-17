import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAggregatesGlobalArray

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode}
  {siteTargets : List BlockId} {initial : LS} {upper : Prov}
theorem expressionOccurrence_arrayLiteral {type : Ty} {elements : List Expr}
    (tables : SourceRootTables typingEnv env)
    (children : ∀ expression ∈ elements, ∀ state provenance,
      ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets expression state provenance) :
    ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets (.arrLit type elements) initial upper := by
  exact globalExpressionOccurrence_arrayLiteral tables children

#print axioms expressionOccurrence_arrayLiteral

end Goose.Lower.Validation.ReplacementContentFlowSource
