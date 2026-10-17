import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceScalarsGlobalLeaves

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} {initial : LS} {upper : Prov}
theorem expressionOccurrence_literal (integer : IntTy) (value : Int) :
    ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets (.lit integer value) initial upper := by
  exact globalExpressionOccurrence_literal integer value

theorem expressionOccurrence_boolean (value : Bool) :
    ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets (.bool value) initial upper := by
  exact globalExpressionOccurrence_boolean value

#print axioms expressionOccurrence_literal
#print axioms expressionOccurrence_boolean

end Goose.Lower.Validation.ReplacementContentFlowSource
