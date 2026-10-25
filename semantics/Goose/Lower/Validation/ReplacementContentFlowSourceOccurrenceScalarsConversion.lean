import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceScalarsGlobalConversion

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} {initial : LS} {upper : Prov}
theorem expressionOccurrence_conversion {operand : Expr} (kind : ConvKind) (destination : Ty) (origin : OriginId)
    (tables : SourceRootTables typingEnv env)
    (child : ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets operand initial upper) :
    ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets (.conv kind destination operand origin) initial upper := by
  exact globalExpressionOccurrence_conversion kind destination origin tables child

#print axioms expressionOccurrence_conversion

end Goose.Lower.Validation.ReplacementContentFlowSource
