import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceScalarsGlobalUnary

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} {initial : LS} {upper : Prov}

theorem expressionOccurrence_unary {operand : Expr} (op : UnOp) (origin : OriginId)
    (tables : SourceRootTables typingEnv env)
    (child : ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets operand initial upper) :
    ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets (.un op operand origin) initial upper := by
  exact globalExpressionOccurrence_unary op origin tables child

theorem expressionOccurrence_not {operand : Expr}
    (tables : SourceRootTables typingEnv env)
    (child : ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets operand initial upper) :
    ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets (.not operand) initial upper := by
  exact globalExpressionOccurrence_not tables child

#print axioms expressionOccurrence_unary
#print axioms expressionOccurrence_not

end Goose.Lower.Validation.ReplacementContentFlowSource
