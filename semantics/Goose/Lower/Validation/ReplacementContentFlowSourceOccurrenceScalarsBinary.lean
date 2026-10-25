import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceScalarsGlobalBinary

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} {initial : LS} {upper : Prov}
theorem expressionOccurrence_binary {left right : Expr} (op : BinOp) (origin : OriginId)
    (tables : SourceRootTables typingEnv env)
    (leftChild : ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets left initial upper)
    (rightChild : ∀ provenance, ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets right
      (lowerExpr left (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 provenance) :
    ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets (.bin op left right origin) initial upper := by
  exact globalExpressionOccurrence_binary op origin tables leftChild rightChild

#print axioms expressionOccurrence_binary

end Goose.Lower.Validation.ReplacementContentFlowSource
