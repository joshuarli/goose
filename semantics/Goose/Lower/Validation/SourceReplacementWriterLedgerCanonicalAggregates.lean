import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalAggregatesArray
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalAggregatesStruct
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalAggregatesFill

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}
  {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode}
  {siteTargets : List BlockId} {initial : LS} {upper : Prov}

theorem canonical_expressionOccurrence_arrayLiteral {type : Ty} {elements : List Expr}
    (tables : SourceRootTables typingEnv env)
    (children : ∀ expression ∈ elements, ∀ state provenance,
      CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets expression state provenance) :
    CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets (.arrLit type elements) initial upper := by
  exact canonical_globalExpressionOccurrence_arrayLiteral tables children

theorem canonical_expressionOccurrence_structLiteral {type : Ty} {elements : List Expr}
    (tables : SourceRootTables typingEnv env)
    (children : ∀ expression ∈ elements, ∀ state provenance,
      CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets expression state provenance) :
    CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets (.structLit type elements) initial upper := by
  exact canonical_globalExpressionOccurrence_structLiteral tables children

theorem canonical_expressionOccurrence_arrayFill {type : Ty} {element : Expr}
    (tables : SourceRootTables typingEnv env)
    (child : CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets element initial upper) :
    CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets (.fill type element) initial upper := by
  exact canonical_globalExpressionOccurrence_arrayFill tables child

#print axioms canonical_expressionOccurrence_arrayLiteral
#print axioms canonical_expressionOccurrence_structLiteral
#print axioms canonical_expressionOccurrence_arrayFill

end Goose.Lower.Validation.SourceReplacementWriterLedger
