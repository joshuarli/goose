import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalReference
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalLength
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalSlice
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalCall
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalScalars
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalAggregates
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalPushPop
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalAccess
import Goose.Lower.Validation.SourceOccurrenceInductionContext
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalSpecialize
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalWhole
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalBlocks
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalStatements
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalControlGlobalExpressionStatement
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalStorageLet
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalStorageRebind
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalStorageAssign
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalStorageAssignOp
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalMutationsGrowth
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalMutationsCounts
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalMutationsResize
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalMutationsOwners
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalStorageReturn
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalStorageReturnUnit
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalStoragePrint
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalControlTransfers
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalControlAbort
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalControls
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalOrdinaryLeaves
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalOrdinaryLists

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation ReplacementContentFlowSource

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}

variable {typingEnv : TEnv} {env : PEnv} {context : ContextId}
  {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId}

theorem canonical_source_expression_replay_step {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (parent : Expr)
    (expressionChild : ∀ {typingEnv : TEnv} {siteTargets : List BlockId} (expression : Expr) (_smaller : sizeOf expression < sizeOf parent)
    (_source : SourceContextEnvironment typingEnv env context)
    (_validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (_bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (_scopes : SourceScopesWithin scopeCount (Core.exprScopes none expression)),
    ∀ initial upper, CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets expression initial upper)
    (placeChild : ∀ {typingEnv : TEnv} {siteTargets : List BlockId} (place : Place) (_smaller : sizeOf place < sizeOf parent)
    (_source : SourceContextEnvironment typingEnv env context)
    (_validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (_bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (_scopes : SourceScopesWithin scopeCount (Core.placeScopes none place)),
    ∀ initial upper, CanonicalPlaceOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets place initial upper)
    (viewChild : ∀ {typingEnv : TEnv} {siteTargets : List BlockId} (view : View) (_smaller : sizeOf view < sizeOf parent)
    (_source : SourceContextEnvironment typingEnv env context)
    (_validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (_bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (_scopes : SourceScopesWithin scopeCount (Core.viewScopes none view)),
    ∀ initial upper, CanonicalViewOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets view initial upper)
    (boundChild : ∀ {typingEnv : TEnv} {siteTargets : List BlockId} (bound : Bound) (_smaller : sizeOf bound < sizeOf parent)
    (_source : SourceContextEnvironment typingEnv env context)
    (_validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (_bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (_scopes : SourceScopesWithin scopeCount (Core.boundScopes none bound)),
    ∀ initial upper, CanonicalBoundOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets bound initial upper)
    (blockChild : ∀ {typingEnv : TEnv} {siteTargets : List BlockId} (body : Core.Block) (_smaller : sizeOf body < sizeOf parent)
    (_source : SourceContextEnvironment typingEnv env context)
    (_validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (_bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (_scopes : SourceScopesWithin scopeCount (Core.blockScopes none body)),
    ∀ loop bindings want initial upper,
      CanonicalBlockOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets loop bindings want body initial upper)
    (expressionsChild : ∀ {typingEnv : TEnv} {siteTargets : List BlockId} (expressions : List Expr) (_smaller : sizeOf expressions < sizeOf parent)
    (_source : SourceContextEnvironment typingEnv env context)
    (_validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (_bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (_scopes : SourceScopesWithin scopeCount (Core.exprsScopes none expressions)),
    ∀ expression ∈ expressions, ∀ initial upper,
      CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets expression initial upper)
    (argumentsChild : ∀ {typingEnv : TEnv} {siteTargets : List BlockId} (arguments : List Arg) (_smaller : sizeOf arguments < sizeOf parent)
    (_source : SourceContextEnvironment typingEnv env context)
    (_validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (_bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (_scopes : SourceScopesWithin scopeCount (Core.argsScopes none arguments)),
    ∀ argument ∈ arguments, ∀ initial upper,
      match argument with
      | .byVal expression => CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets expression initial upper
      | .byRef _ place => CanonicalPlaceOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets place initial upper)
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.exprScopes none parent)) :
    ∀ initial upper, CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets parent initial upper := by
  intro initial upper
  cases parent with
  | lit integer value =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact canonical_expressionOccurrence_literal integer value
  | bool value =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact canonical_expressionOccurrence_boolean value
  | read place =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact canonical_occurrenceReplay_read source
      (placeChild place (by decreasing_tactic) source validity bounded scopedBounds) initial upper
  | ref mutability place =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact canonical_occurrenceReplay_reference mutability source (placeChild place (by decreasing_tactic) source validity bounded scopedBounds) initial upper
  | slice mutability view low high origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    have first := SourceScopesWithin.append.mp parts.1
    exact canonical_occurrenceReplay_slice mutability origin source
      (viewChild view (by decreasing_tactic) source validity bounded first.1)
      (boundChild low (by decreasing_tactic) source validity bounded first.2)
      (boundChild high (by decreasing_tactic) source validity bounded parts.2) initial upper
  | len view =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact canonical_occurrenceReplay_length source (viewChild view (by decreasing_tactic) source validity bounded scopedBounds) initial upper
  | un op operand origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact canonical_expressionOccurrence_unary op origin source.tables (expressionChild operand (by decreasing_tactic) source validity bounded scopedBounds initial upper)
  | bin op left right origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact canonical_expressionOccurrence_binary op origin source.tables
      (expressionChild left (by decreasing_tactic) source validity bounded parts.1 initial upper)
      (fun provenance => expressionChild right (by decreasing_tactic) source validity bounded parts.2 _ provenance)
  | cmp op left right =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact canonical_expressionOccurrence_comparison op source.tables
      (expressionChild left (by decreasing_tactic) source validity bounded parts.1 initial upper)
      (fun provenance => expressionChild right (by decreasing_tactic) source validity bounded parts.2 _ provenance)
  | and left right =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact canonical_expressionOccurrence_shortCircuit true
      (expressionChild left (by decreasing_tactic) source validity bounded parts.1 initial upper)
      (fun targets provenance => expressionChild (siteTargets := targets) right (by decreasing_tactic) source validity bounded parts.2 _ provenance)
  | or left right =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact canonical_expressionOccurrence_shortCircuit false
      (expressionChild left (by decreasing_tactic) source validity bounded parts.1 initial upper)
      (fun targets provenance => expressionChild (siteTargets := targets) right (by decreasing_tactic) source validity bounded parts.2 _ provenance)
  | not operand =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact canonical_expressionOccurrence_not source.tables (expressionChild operand (by decreasing_tactic) source validity bounded scopedBounds initial upper)
  | conv kind destination operand origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact canonical_expressionOccurrence_conversion kind destination origin source.tables
      (expressionChild operand (by decreasing_tactic) source validity bounded scopedBounds initial upper)
  | call callee args origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    apply canonical_expressionOccurrence_call source validity bounded
    · intro operand member state provenance
      exact argumentsChild args (by decreasing_tactic) source validity bounded scopedBounds (.byVal operand) member state provenance
    · intro mutability place member state provenance
      exact argumentsChild args (by decreasing_tactic) source validity bounded scopedBounds (.byRef mutability place) member state provenance
  | push owner operand origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact canonical_expressionOccurrence_push origin source.tables source.readable source.parameters
      (placeChild owner (by decreasing_tactic) source validity bounded parts.1 initial upper)
      (fun provenance => expressionChild operand (by decreasing_tactic) source validity bounded parts.2 _ provenance)
  | pop owner origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact canonical_expressionOccurrence_pop origin source.tables source.parameters
      (placeChild owner (by decreasing_tactic) source validity bounded scopedBounds initial upper)
  | ifE condition yes no =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    have first := SourceScopesWithin.append.mp parts.1
    apply canonical_expressionOccurrence_if source validity first.2 parts.2
      (expressionChild condition (by decreasing_tactic) source validity bounded first.1 initial upper)
    intro body member state provenance
    rcases member with rfl | rfl
    · exact blockChild body (by decreasing_tactic) source.expression validity bounded first.2 _ _ _ state provenance
    · exact blockChild body (by decreasing_tactic) source.expression validity bounded parts.2 _ _ _ state provenance
  | blockE body =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact canonical_expressionOccurrence_block scopedBounds (blockChild body (by decreasing_tactic) source.expression validity bounded scopedBounds _ _ _ initial upper)
  | arrLit type elements =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    apply canonical_expressionOccurrence_arrayLiteral source.tables
    exact expressionsChild elements (by decreasing_tactic) source validity bounded scopedBounds
  | structLit type elements =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    apply canonical_expressionOccurrence_structLiteral source.tables
    exact expressionsChild elements (by decreasing_tactic) source validity bounded scopedBounds
  | fill type operand =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact canonical_expressionOccurrence_arrayFill source.tables (expressionChild operand (by decreasing_tactic) source validity bounded scopedBounds initial upper)

#print axioms canonical_source_expression_replay_step

end Goose.Lower.Validation.SourceReplacementWriterLedger
