import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalOrdinaryLeaves
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalScalarsUnary
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalScalarsBinary
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalScalarsComparison
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalScalarsConversion

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}
  {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode}
  {siteTargets : List BlockId} {initial : LS} {upper : Prov}

theorem canonical_expressionOccurrence_literal (integer : IntTy) (value : Int) :
    CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets (.lit integer value) initial upper := by
  exact canonical_globalExpressionOccurrence_literal integer value

theorem canonical_expressionOccurrence_boolean (value : Bool) :
    CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets (.bool value) initial upper := by
  exact canonical_globalExpressionOccurrence_boolean value

theorem canonical_expressionOccurrence_unary {operand : Expr} (op : UnOp) (origin : OriginId)
    (tables : SourceRootTables typingEnv env)
    (child : CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets operand initial upper) :
    CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets (.un op operand origin) initial upper := by
  exact canonical_globalExpressionOccurrence_unary op origin tables child

theorem canonical_expressionOccurrence_not {operand : Expr}
    (tables : SourceRootTables typingEnv env)
    (child : CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets operand initial upper) :
    CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets (.not operand) initial upper := by
  exact canonical_globalExpressionOccurrence_not tables child

theorem canonical_expressionOccurrence_binary {left right : Expr} (op : BinOp) (origin : OriginId)
    (tables : SourceRootTables typingEnv env)
    (leftChild : CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets left initial upper)
    (rightChild : ∀ provenance, CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets right
      (lowerExpr left (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 provenance) :
    CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets (.bin op left right origin) initial upper := by
  exact canonical_globalExpressionOccurrence_binary op origin tables leftChild rightChild

theorem canonical_expressionOccurrence_comparison {left right : Expr} (op : CmpOp)
    (tables : SourceRootTables typingEnv env)
    (leftChild : CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets left initial upper)
    (rightChild : ∀ provenance, CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets right
      (lowerExpr left (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 provenance) :
    CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets (.cmp op left right) initial upper := by
  exact canonical_globalExpressionOccurrence_comparison op tables leftChild rightChild

theorem canonical_expressionOccurrence_conversion {operand : Expr} (kind : ConvKind) (destination : Ty) (origin : OriginId)
    (tables : SourceRootTables typingEnv env)
    (child : CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets operand initial upper) :
    CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets (.conv kind destination operand origin) initial upper := by
  exact canonical_globalExpressionOccurrence_conversion kind destination origin tables child

#print axioms canonical_expressionOccurrence_literal
#print axioms canonical_expressionOccurrence_boolean
#print axioms canonical_expressionOccurrence_unary
#print axioms canonical_expressionOccurrence_not
#print axioms canonical_expressionOccurrence_binary
#print axioms canonical_expressionOccurrence_comparison
#print axioms canonical_expressionOccurrence_conversion

end Goose.Lower.Validation.SourceReplacementWriterLedger
