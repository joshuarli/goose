import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAggregatesGlobalStruct

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode}
  {siteTargets : List BlockId} {initial : LS} {upper : Prov}
theorem expressionOccurrence_structLiteral {type : Ty} {elements : List Expr}
    (tables : SourceRootTables typingEnv env)
    (children : ∀ expression ∈ elements, ∀ state provenance,
      ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets expression state provenance) :
    ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets (.structLit type elements) initial upper := by
  exact globalExpressionOccurrence_structLiteral tables children

#print axioms expressionOccurrence_structLiteral

end Goose.Lower.Validation.ReplacementContentFlowSource
