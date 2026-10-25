import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalExpressionStep
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalStatementStep
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

mutual

theorem canonical_source_expression_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (expression : Expr)
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.exprScopes none expression)) :
    ∀ initial upper, CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets expression initial upper := by
  apply canonical_source_expression_replay_step expression
  · intro nextTyping targets expression smaller source validity bounded scopes
    exact canonical_source_expression_occurrence_replay expression source validity bounded scopes
  · intro nextTyping targets place smaller source validity bounded scopes
    exact canonical_source_place_occurrence_replay place source validity bounded scopes
  · intro nextTyping targets view smaller source validity bounded scopes
    exact canonical_source_view_occurrence_replay view source validity bounded scopes
  · intro nextTyping targets bound smaller source validity bounded scopes
    exact canonical_source_bound_occurrence_replay bound source validity bounded scopes
  · intro nextTyping targets body smaller source validity bounded scopes
    exact canonical_source_block_occurrence_replay body source validity bounded scopes
  · intro nextTyping targets expressions smaller source validity bounded scopes
    exact canonical_source_expressions_occurrence_replay expressions source validity bounded scopes
  · intro nextTyping targets arguments smaller source validity bounded scopes
    exact canonical_source_arguments_occurrence_replay arguments source validity bounded scopes
  · exact source
  · exact validity
  · exact bounded
  · exact scopes
termination_by sizeOf expression

theorem canonical_source_place_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (place : Place)
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.placeScopes none place)) :
    ∀ initial upper, CanonicalPlaceOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets place initial upper := by
  apply canonical_occurrenceReplay_place place source
  · intro owner field same
    cases same
    exact canonical_source_place_occurrence_replay owner source validity bounded scopes
  · intro view index origin same
    cases same
    exact canonical_source_view_occurrence_replay view source validity bounded (SourceScopesWithin.append.mp scopes).1
  · intro expression state provenance occurrence
    rcases occurrence with rfl | ⟨view, origin, rfl⟩
    · exact canonical_source_expression_occurrence_replay expression source validity bounded scopes state provenance
    · exact canonical_source_expression_occurrence_replay expression source validity bounded (SourceScopesWithin.append.mp scopes).2 state provenance
termination_by sizeOf place

theorem canonical_source_view_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (view : View)
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.viewScopes none view)) :
    ∀ initial upper, CanonicalViewOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets view initial upper := by
  apply canonical_occurrenceReplay_view view source
  · intro place same
    cases same
    exact canonical_source_place_occurrence_replay place source validity bounded scopes
  · intro expression same
    cases same
    exact canonical_source_expression_occurrence_replay expression source validity bounded scopes
termination_by sizeOf view

theorem canonical_source_bound_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (bound : Bound)
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.boundScopes none bound)) :
    ∀ initial upper, CanonicalBoundOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets bound initial upper := by
  apply canonical_occurrenceReplay_bound bound source
  intro expression occurrence
  rcases occurrence with rfl | rfl
  all_goals exact canonical_source_expression_occurrence_replay expression source validity bounded scopes
termination_by sizeOf bound

theorem canonical_source_expressions_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (expressions : List Expr)
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.exprsScopes none expressions)) :
    ∀ expression ∈ expressions, ∀ initial upper,
      CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets expression initial upper := by
  cases expressions with
  | nil => simp
  | cons first rest =>
    intro expression member
    rcases List.mem_cons.mp member with rfl | member
    · exact canonical_source_expression_occurrence_replay expression source validity bounded (SourceScopesWithin.append.mp scopes).1
    · exact canonical_source_expressions_occurrence_replay rest source validity bounded (SourceScopesWithin.append.mp scopes).2 expression member
termination_by sizeOf expressions
decreasing_by
  all_goals try decreasing_trivial
  all_goals try subst expressions
  all_goals try subst expression
  all_goals simp +arith

theorem canonical_source_arguments_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (arguments : List Arg)
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.argsScopes none arguments)) :
    ∀ argument ∈ arguments, ∀ initial upper,
      match argument with
      | .byVal expression => CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets expression initial upper
      | .byRef _ place => CanonicalPlaceOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets place initial upper := by
  cases arguments with
  | nil => simp
  | cons first rest =>
    intro argument member
    rcases List.mem_cons.mp member with same | restMember
    · subst argument
      cases first with
      | byVal expression => exact canonical_source_expression_occurrence_replay expression source validity bounded (SourceScopesWithin.append.mp scopes).1
      | byRef mutability place => exact canonical_source_place_occurrence_replay place source validity bounded (SourceScopesWithin.append.mp scopes).1
    · cases first with
      | byVal expression => exact canonical_source_arguments_occurrence_replay rest source validity bounded (SourceScopesWithin.append.mp scopes).2 argument restMember
      | byRef mutability place => exact canonical_source_arguments_occurrence_replay rest source validity bounded (SourceScopesWithin.append.mp scopes).2 argument restMember
termination_by sizeOf arguments

theorem canonical_source_block_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (body : Core.Block)
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.blockScopes none body)) :
    ∀ loop bindings want initial upper,
      CanonicalBlockOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets loop bindings want body initial upper := by
  intro loop bindings want initial upper
  cases body with
  | mk scope statements value =>
    apply canonical_blockOccurrence_of_children
    · intro nextEnv moduleEq variablesEq implEq modeEq state provenance
      exact canonical_source_statements_occurrence_replay statements
        ((source.typingTables moduleEq variablesEq implEq).scopes (scope :: env.scopes)) validity bounded
        ((SourceScopesWithin.statements_parent statements (some scope) none).mp
          (SourceScopesWithin.block_parts scopes).2.1) loop (.block (.mk scope statements value)) scope state provenance
    · intro expression present expressionScopes nextEnv moduleEq variablesEq implEq modeEq state provenance
      exact canonical_source_expression_occurrence_replay expression
        ((source.typingTables moduleEq variablesEq implEq).scopes (scope :: env.scopes)) validity bounded expressionScopes state provenance
termination_by sizeOf body

theorem canonical_source_statements_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (statements : List Stmt)
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.stmtsScopes none statements)) :
    ∀ loop root scope initial upper,
      CanonicalStatementsOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets loop root scope statements initial upper := by
  intro loop root scope initial upper
  apply canonical_statementsOccurrence_of_statement
  intro statement member nextEnv moduleEq variablesEq implEq modeEq state provenance
  exact canonical_source_statement_occurrence_replay statement (source.typingTables moduleEq variablesEq implEq) validity bounded
    (SourceScopesWithin.stmts_member scopes member) loop scope state provenance
termination_by sizeOf statements

theorem canonical_source_printargs_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (arguments : List PrintArg)
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.printScopes none arguments)) :
    ∀ expression, PrintArg.expr expression ∈ arguments → ∀ initial upper,
      CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets expression initial upper := by
  cases arguments with
  | nil => simp
  | cons first rest =>
    intro expression member
    cases first with
    | text text =>
      exact canonical_source_printargs_occurrence_replay rest source validity bounded scopes expression (by simpa using member)
    | expr first =>
      rcases List.mem_cons.mp member with same | member
      · cases PrintArg.expr.inj same
        exact canonical_source_expression_occurrence_replay expression source validity bounded (SourceScopesWithin.append.mp scopes).1
      · exact canonical_source_printargs_occurrence_replay rest source validity bounded (SourceScopesWithin.append.mp scopes).2 expression member
termination_by sizeOf arguments

theorem canonical_source_statement_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (statement : Stmt)
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.stmtScopes none statement)) :
    ∀ loop scope initial upper,
      CanonicalStatementOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets loop scope statement initial upper := by
  apply canonical_source_statement_replay_step statement
  · intro nextTyping targets expression smaller source validity bounded scopes
    exact canonical_source_expression_occurrence_replay expression source validity bounded scopes
  · intro nextTyping targets place smaller source validity bounded scopes
    exact canonical_source_place_occurrence_replay place source validity bounded scopes
  · intro nextTyping targets view smaller source validity bounded scopes
    exact canonical_source_view_occurrence_replay view source validity bounded scopes
  · intro nextTyping targets body smaller source validity bounded scopes
    exact canonical_source_block_occurrence_replay body source validity bounded scopes
  · intro nextTyping targets arguments smaller source validity bounded scopes
    exact canonical_source_printargs_occurrence_replay arguments source validity bounded scopes
  · exact source
  · exact validity
  · exact bounded
  · exact scopes
termination_by sizeOf statement

end

#print axioms canonical_source_expression_occurrence_replay
#print axioms canonical_source_place_occurrence_replay
#print axioms canonical_source_view_occurrence_replay
#print axioms canonical_source_bound_occurrence_replay
#print axioms canonical_source_block_occurrence_replay
#print axioms canonical_source_statements_occurrence_replay
#print axioms canonical_source_statement_occurrence_replay
#print axioms canonical_source_expressions_occurrence_replay
#print axioms canonical_source_arguments_occurrence_replay
#print axioms canonical_source_printargs_occurrence_replay

end Goose.Lower.Validation.SourceReplacementWriterLedger
