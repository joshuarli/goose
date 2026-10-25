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

theorem canonical_source_statement_replay_step {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (statement : Stmt)
    (expressionChild : ∀ {typingEnv : TEnv} {siteTargets : List BlockId} (expression : Expr) (_smaller : sizeOf expression < sizeOf statement)
    (_source : SourceContextEnvironment typingEnv env context)
    (_validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (_bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (_scopes : SourceScopesWithin scopeCount (Core.exprScopes none expression)),
    ∀ initial upper, CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets expression initial upper)
    (placeChild : ∀ {typingEnv : TEnv} {siteTargets : List BlockId} (place : Place) (_smaller : sizeOf place < sizeOf statement)
    (_source : SourceContextEnvironment typingEnv env context)
    (_validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (_bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (_scopes : SourceScopesWithin scopeCount (Core.placeScopes none place)),
    ∀ initial upper, CanonicalPlaceOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets place initial upper)
    (viewChild : ∀ {typingEnv : TEnv} {siteTargets : List BlockId} (view : View) (_smaller : sizeOf view < sizeOf statement)
    (_source : SourceContextEnvironment typingEnv env context)
    (_validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (_bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (_scopes : SourceScopesWithin scopeCount (Core.viewScopes none view)),
    ∀ initial upper, CanonicalViewOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets view initial upper)
    (blockChild : ∀ {typingEnv : TEnv} {siteTargets : List BlockId} (body : Core.Block) (_smaller : sizeOf body < sizeOf statement)
    (_source : SourceContextEnvironment typingEnv env context)
    (_validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (_bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (_scopes : SourceScopesWithin scopeCount (Core.blockScopes none body)),
    ∀ loop bindings want initial upper,
      CanonicalBlockOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets loop bindings want body initial upper)
    (printargsChild : ∀ {typingEnv : TEnv} {siteTargets : List BlockId} (arguments : List PrintArg) (_smaller : sizeOf arguments < sizeOf statement)
    (_source : SourceContextEnvironment typingEnv env context)
    (_validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (_bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (_scopes : SourceScopesWithin scopeCount (Core.printScopes none arguments)),
    ∀ expression, PrintArg.expr expression ∈ arguments → ∀ initial upper,
      CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets expression initial upper)
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.stmtScopes none statement)) :
    ∀ loop scope initial upper,
      CanonicalStatementOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets loop scope statement initial upper := by
  intro loop scope initial upper
  cases statement with
  | letS variableId expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact canonical_statementOccurrence_let source.tables source.contextOk
      (expressionChild expression (by decreasing_tactic) source validity bounded scopedBounds initial upper)
  | rebind variableId expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact canonical_statementOccurrence_rebind source.tables source.accepted source.implementationRow source.contextOk
      (expressionChild expression (by decreasing_tactic) source validity bounded scopedBounds initial upper)
  | expr expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact canonical_statementOccurrence_expression (expressionChild expression (by decreasing_tactic) source validity bounded scopedBounds initial upper)
  | assign owner expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    apply canonical_statement_occurrence_context_of_global
    exact canonical_statementOccurrence_assign origin loop scope source.tables source.parameters (referenceSlicePlaceOccurrence_of_context source)
      (placeChild owner (by decreasing_tactic) source validity bounded parts.1 initial upper)
      (fun provenance => expressionChild expression (by decreasing_tactic) source validity bounded parts.2 _ provenance)
  | assignOp op owner expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    apply canonical_statement_occurrence_context_of_global
    exact canonical_statementOccurrence_assignOp op origin loop scope source.tables source.parameters
      (placeChild owner (by decreasing_tactic) source validity bounded parts.1 initial upper)
      (fun provenance => expressionChild expression (by decreasing_tactic) source validity bounded parts.2 _ provenance)
  | assignWhole owner expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    apply canonical_statement_occurrence_context_of_global
    exact canonical_statementOccurrence_assignWhole origin loop scope source.tables source.parameters
      (placeChild owner (by decreasing_tactic) source validity bounded parts.1 initial upper)
      (fun provenance => expressionChild expression (by decreasing_tactic) source validity bounded parts.2 _ provenance)
  | append owner view origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    apply canonical_statement_occurrence_context_of_global
    exact canonical_statementOccurrence_append origin loop scope source.tables source.parameters
      (placeChild owner (by decreasing_tactic) source validity bounded parts.1 initial upper)
      (fun provenance => viewChild view (by decreasing_tactic) source validity bounded parts.2 _ provenance)
  | popN owner count origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    apply canonical_statement_occurrence_context_of_global
    exact canonical_statementOccurrence_popN origin loop scope source.tables source.parameters
      (placeChild owner (by decreasing_tactic) source validity bounded parts.1 initial upper)
      (fun provenance => expressionChild count (by decreasing_tactic) source validity bounded parts.2 _ provenance)
  | resize owner count fill origin =>
    cases fill with
    | none =>
      have scopedBounds := scopes
      simp only [Core.stmtScopes] at scopedBounds
      have parts := SourceScopesWithin.append.mp (SourceScopesWithin.append.mp scopedBounds).1
      apply canonical_statement_occurrence_context_of_global
      exact canonical_statementOccurrence_resizeWithoutFill origin loop scope source.tables source.parameters
        (placeChild owner (by decreasing_tactic) source validity bounded parts.1 initial upper)
        (fun provenance => expressionChild count (by decreasing_tactic) source validity bounded parts.2 _ provenance)
    | some fill =>
      have scopedBounds := scopes
      simp only [Core.stmtScopes] at scopedBounds
      have parts := SourceScopesWithin.append.mp scopedBounds
      have first := SourceScopesWithin.append.mp parts.1
      apply canonical_statement_occurrence_context_of_global
      exact canonical_statementOccurrence_resizeWithFill origin loop scope source.tables source.readable source.parameters
        (placeChild owner (by decreasing_tactic) source validity bounded first.1 initial upper)
        (fun provenance => expressionChild count (by decreasing_tactic) source validity bounded first.2 _ provenance)
        (fun provenance => expressionChild fill (by decreasing_tactic) source validity bounded parts.2 _ provenance)
  | clear owner origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    apply canonical_statement_occurrence_context_of_global
    exact canonical_statementOccurrence_clear origin loop scope source.tables source.parameters
      (placeChild owner (by decreasing_tactic) source validity bounded scopedBounds initial upper)
  | ifS condition yes no origin =>
    cases no with
    | none =>
      have scopedBounds := scopes
      simp only [Core.stmtScopes, List.append_nil] at scopedBounds
      have parts := SourceScopesWithin.append.mp scopedBounds
      apply canonical_statementOccurrence_if (expressionChild condition (by decreasing_tactic) source validity bounded parts.1 initial upper)
      intro body member targets state provenance
      rcases member with same | impossible
      · subst body
        exact blockChild (siteTargets := targets) yes (by decreasing_tactic) source validity bounded parts.2 loop [] false state provenance
      · cases impossible
    | some no =>
      have scopedBounds := scopes
      simp only [Core.stmtScopes] at scopedBounds
      have parts := SourceScopesWithin.append.mp scopedBounds
      have first := SourceScopesWithin.append.mp parts.1
      apply canonical_statementOccurrence_if (expressionChild condition (by decreasing_tactic) source validity bounded first.1 initial upper)
      intro body member targets state provenance
      rcases member with same | same
      · subst body
        exact blockChild (siteTargets := targets) yes (by decreasing_tactic) source validity bounded first.2 loop [] false state provenance
      · have identity : body = no := (Option.some.inj same).symm
        subst body
        exact blockChild (siteTargets := targets) no (by decreasing_tactic) source validity bounded parts.2 loop [] false state provenance
  | «while» condition body origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    apply canonical_statementOccurrence_while
    · intro targets
      exact expressionChild (siteTargets := targets) condition (by decreasing_tactic) source validity bounded parts.1 _ upper
    · intro targets provenance
      exact blockChild (siteTargets := targets) body (by decreasing_tactic) (source.typingTables (nextEnv := { typingEnv with loops := typingEnv.loops + 1 }) rfl rfl rfl) validity bounded parts.2 _ [] false _ provenance
  | forRange variableId low high body origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    have first := SourceScopesWithin.append.mp parts.1
    apply canonical_statementOccurrence_range source.tables
      (expressionChild low (by decreasing_tactic) source validity bounded first.1 initial upper)
      (fun provenance => expressionChild high (by decreasing_tactic) source validity bounded first.2 _ provenance)
    intro targets depth header exit type counter state provenance
    dsimp only
    intro typeEq headerEq counterEq stateEq
    exact blockChild (siteTargets := targets) body (by decreasing_tactic) (source.typingTables (nextEnv := { typingEnv with loops := typingEnv.loops + 1, visible := variableId :: typingEnv.visible }) rfl rfl rfl) validity bounded parts.2 _ _ false state provenance
  | forEach variableId index view byRef body origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    apply canonical_statementOccurrence_each source.readable source.tables source.contextOk.annotationShape source.parameters
    · intro place same
      cases same
      exact placeChild place (by decreasing_tactic) source validity bounded parts.1 initial upper
    · intro expression same
      cases same
      exact expressionChild expression (by decreasing_tactic) source validity bounded parts.1 initial upper
    · intro targets depth header exit counter value state provenance
      dsimp only
      intro headerEq counterEq valueEq stateEq
      exact blockChild (siteTargets := targets) body (by decreasing_tactic) (source.typingTables (nextEnv := { typingEnv with loops := typingEnv.loops + 1, visible := variableId :: index.toList ++ typingEnv.visible }) rfl rfl rfl) validity bounded parts.2 _ _ false state provenance
  | ret expression origin =>
    cases expression with
    | none => exact canonical_statementOccurrence_returnUnit source.tables
    | some expression =>
        have scopedBounds := scopes
        simp only [Core.stmtScopes] at scopedBounds
        exact canonical_statementOccurrence_return source.tables source.implementation source.implementationRow source.contextOk
          (expressionChild expression (by decreasing_tactic) source validity bounded scopedBounds initial upper)
  | brk origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact canonical_statementOccurrence_break
  | cont origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact canonical_statementOccurrence_continue
  | print arguments origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    apply canonical_statement_occurrence_context_of_global
    exact canonical_statementOccurrence_print source.tables (printargsChild arguments (by decreasing_tactic) source validity bounded scopedBounds)
  | assertS expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact canonical_statementOccurrence_assert origin source.tables (expressionChild expression (by decreasing_tactic) source validity bounded scopedBounds initial upper)
  | abort message origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact canonical_statementOccurrence_abort message origin source.tables
  | exit expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact canonical_statementOccurrence_exit origin source.tables (expressionChild expression (by decreasing_tactic) source validity bounded scopedBounds initial upper)

#print axioms canonical_source_statement_replay_step

end Goose.Lower.Validation.SourceReplacementWriterLedger
