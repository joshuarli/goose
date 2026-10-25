import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAggregatesGlobalFill

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} {initial : LS} {upper : Prov}
theorem expressionOccurrence_arrayFill {type : Ty} {element : Expr}
    (tables : SourceRootTables typingEnv env)
    (child : ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets element initial upper) :
    ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets (.fill type element) initial upper := by
  exact globalExpressionOccurrence_arrayFill tables child

#print axioms expressionOccurrence_arrayFill

end Goose.Lower.Validation.ReplacementContentFlowSource
