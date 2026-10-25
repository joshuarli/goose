import Goose.Lower.Validation.SourceCanonicalRootFloorsWriteLookup
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessRead
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessReference
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessLength
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessSlice
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessBounds
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrencePlaces
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceViews
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceCalls
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceStorage
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceStorageReferencePlace
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlIfExpression
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlShortCircuit
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlBlocks
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlBlockExpression
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlAbort
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlExpressionStatement
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceLoopsWhile
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceLoopsRange
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceLoopsEach
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlContracts
import Goose.Lower.Validation.SummaryPreservationSourceContextEnvironment
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceScalars
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAggregates
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceMutationsBasic
import Goose.Lower.Validation.SourceOccurrenceInductionSpecialize
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlTransfers
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlStatements
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlIf

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {context : ContextId}
  {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId}

set_option maxHeartbeats 1200000

mutual

theorem source_expression_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (expression : Expr)
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.exprScopes none expression)) :
    ∀ initial upper, ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets expression initial upper := by
  intro initial upper
  cases expression with
  | lit integer value =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact expressionOccurrence_literal integer value
  | bool value =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact expressionOccurrence_boolean value
  | read place =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact occurrenceReplay_read source
      (source_place_occurrence_replay place source validity bounded scopedBounds) initial upper
  | ref mutability place =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact occurrenceReplay_reference mutability source (source_place_occurrence_replay place source validity bounded scopedBounds) initial upper
  | slice mutability view low high origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    have first := SourceScopesWithin.append.mp parts.1
    exact occurrenceReplay_slice mutability origin source
      (source_view_occurrence_replay view source validity bounded first.1)
      (source_bound_occurrence_replay low source validity bounded first.2)
      (source_bound_occurrence_replay high source validity bounded parts.2) initial upper
  | len view =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact occurrenceReplay_length source (source_view_occurrence_replay view source validity bounded scopedBounds) initial upper
  | un op operand origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact expressionOccurrence_unary op origin source.tables (source_expression_occurrence_replay operand source validity bounded scopedBounds initial upper)
  | bin op left right origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact expressionOccurrence_binary op origin source.tables
      (source_expression_occurrence_replay left source validity bounded parts.1 initial upper)
      (fun provenance => source_expression_occurrence_replay right source validity bounded parts.2 _ provenance)
  | cmp op left right =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact expressionOccurrence_comparison op source.tables
      (source_expression_occurrence_replay left source validity bounded parts.1 initial upper)
      (fun provenance => source_expression_occurrence_replay right source validity bounded parts.2 _ provenance)
  | and left right =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact expressionOccurrence_shortCircuit true
      (source_expression_occurrence_replay left source validity bounded parts.1 initial upper)
      (fun targets provenance => source_expression_occurrence_replay (siteTargets := targets) right source validity bounded parts.2 _ provenance)
  | or left right =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact expressionOccurrence_shortCircuit false
      (source_expression_occurrence_replay left source validity bounded parts.1 initial upper)
      (fun targets provenance => source_expression_occurrence_replay (siteTargets := targets) right source validity bounded parts.2 _ provenance)
  | not operand =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact expressionOccurrence_not source.tables (source_expression_occurrence_replay operand source validity bounded scopedBounds initial upper)
  | conv kind destination operand origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact expressionOccurrence_conversion kind destination origin source.tables
      (source_expression_occurrence_replay operand source validity bounded scopedBounds initial upper)
  | call callee args origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    apply expressionOccurrence_call source validity bounded
    · intro operand member state provenance
      exact source_arguments_occurrence_replay args source validity bounded scopedBounds (.byVal operand) member state provenance
    · intro mutability place member state provenance
      exact source_arguments_occurrence_replay args source validity bounded scopedBounds (.byRef mutability place) member state provenance
  | push owner operand origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact expressionOccurrence_push origin source.tables source.readable source.parameters
      (source_place_occurrence_replay owner source validity bounded parts.1 initial upper)
      (fun provenance => source_expression_occurrence_replay operand source validity bounded parts.2 _ provenance)
  | pop owner origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact expressionOccurrence_pop origin source.tables source.parameters
      (source_place_occurrence_replay owner source validity bounded scopedBounds initial upper)
  | ifE condition yes no =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    have first := SourceScopesWithin.append.mp parts.1
    apply expressionOccurrence_if source validity first.2 parts.2
      (source_expression_occurrence_replay condition source validity bounded first.1 initial upper)
    intro body member state provenance
    rcases member with rfl | rfl
    · exact source_block_occurrence_replay body source.expression validity bounded first.2 _ _ _ state provenance
    · exact source_block_occurrence_replay body source.expression validity bounded parts.2 _ _ _ state provenance
  | blockE body =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact expressionOccurrence_block scopedBounds (source_block_occurrence_replay body source.expression validity bounded scopedBounds _ _ _ initial upper)
  | arrLit type elements =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    apply expressionOccurrence_arrayLiteral source.tables
    exact source_expressions_occurrence_replay elements source validity bounded scopedBounds
  | structLit type elements =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    apply expressionOccurrence_structLiteral source.tables
    exact source_expressions_occurrence_replay elements source validity bounded scopedBounds
  | fill type operand =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact expressionOccurrence_arrayFill source.tables (source_expression_occurrence_replay operand source validity bounded scopedBounds initial upper)
termination_by sizeOf expression

theorem source_place_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (place : Place)
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.placeScopes none place)) :
    ∀ initial upper, PlaceOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets place initial upper := by
  apply occurrenceReplay_place place source
  · intro owner field same
    cases same
    exact source_place_occurrence_replay owner source validity bounded scopes
  · intro view index origin same
    cases same
    exact source_view_occurrence_replay view source validity bounded (SourceScopesWithin.append.mp scopes).1
  · intro expression state provenance occurrence
    rcases occurrence with rfl | ⟨view, origin, rfl⟩
    · exact source_expression_occurrence_replay expression source validity bounded scopes state provenance
    · exact source_expression_occurrence_replay expression source validity bounded (SourceScopesWithin.append.mp scopes).2 state provenance
termination_by sizeOf place

theorem source_view_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (view : View)
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.viewScopes none view)) :
    ∀ initial upper, ViewOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets view initial upper := by
  apply occurrenceReplay_view view source
  · intro place same
    cases same
    exact source_place_occurrence_replay place source validity bounded scopes
  · intro expression same
    cases same
    exact source_expression_occurrence_replay expression source validity bounded scopes
termination_by sizeOf view

theorem source_bound_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (bound : Bound)
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.boundScopes none bound)) :
    ∀ initial upper, BoundOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets bound initial upper := by
  apply occurrenceReplay_bound bound source
  intro expression occurrence
  rcases occurrence with rfl | rfl
  all_goals exact source_expression_occurrence_replay expression source validity bounded scopes
termination_by sizeOf bound

theorem source_expressions_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (expressions : List Expr)
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.exprsScopes none expressions)) :
    ∀ expression ∈ expressions, ∀ initial upper,
      ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets expression initial upper := by
  cases expressions with
  | nil => simp
  | cons first rest =>
    intro expression member
    rcases List.mem_cons.mp member with rfl | member
    · exact source_expression_occurrence_replay expression source validity bounded (SourceScopesWithin.append.mp scopes).1
    · exact source_expressions_occurrence_replay rest source validity bounded (SourceScopesWithin.append.mp scopes).2 expression member
termination_by sizeOf expressions
decreasing_by
  all_goals try decreasing_trivial
  all_goals try subst expressions
  all_goals try subst expression
  all_goals simp +arith

theorem source_arguments_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (arguments : List Arg)
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.argsScopes none arguments)) :
    ∀ argument ∈ arguments, ∀ initial upper,
      match argument with
      | .byVal expression => ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets expression initial upper
      | .byRef _ place => PlaceOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets place initial upper := by
  cases arguments with
  | nil => simp
  | cons first rest =>
    intro argument member
    rcases List.mem_cons.mp member with same | restMember
    · subst argument
      cases first with
      | byVal expression => exact source_expression_occurrence_replay expression source validity bounded (SourceScopesWithin.append.mp scopes).1
      | byRef mutability place => exact source_place_occurrence_replay place source validity bounded (SourceScopesWithin.append.mp scopes).1
    · cases first with
      | byVal expression => exact source_arguments_occurrence_replay rest source validity bounded (SourceScopesWithin.append.mp scopes).2 argument restMember
      | byRef mutability place => exact source_arguments_occurrence_replay rest source validity bounded (SourceScopesWithin.append.mp scopes).2 argument restMember
termination_by sizeOf arguments

theorem source_block_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (body : Core.Block)
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.blockScopes none body)) :
    ∀ loop bindings want initial upper,
      BlockOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets loop bindings want body initial upper := by
  intro loop bindings want initial upper
  cases body with
  | mk scope statements value =>
    apply blockOccurrence_of_children
    · intro nextEnv moduleEq variablesEq implEq modeEq state provenance
      exact source_statements_occurrence_replay statements
        ((source.typingTables moduleEq variablesEq implEq).scopes (scope :: env.scopes)) validity bounded
        ((SourceScopesWithin.statements_parent statements (some scope) none).mp
          (SourceScopesWithin.block_parts scopes).2.1) loop (.block (.mk scope statements value)) scope state provenance
    · intro expression present expressionScopes nextEnv moduleEq variablesEq implEq modeEq state provenance
      exact source_expression_occurrence_replay expression
        ((source.typingTables moduleEq variablesEq implEq).scopes (scope :: env.scopes)) validity bounded expressionScopes state provenance
termination_by sizeOf body

theorem source_statements_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (statements : List Stmt)
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.stmtsScopes none statements)) :
    ∀ loop root scope initial upper,
      StatementsOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets loop root scope statements initial upper := by
  intro loop root scope initial upper
  apply statementsOccurrence_of_statement
  intro statement member nextEnv moduleEq variablesEq implEq modeEq state provenance
  exact source_statement_occurrence_replay statement (source.typingTables moduleEq variablesEq implEq) validity bounded
    (SourceScopesWithin.stmts_member scopes member) loop scope state provenance
termination_by sizeOf statements

theorem source_printargs_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (arguments : List PrintArg)
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.printScopes none arguments)) :
    ∀ expression, PrintArg.expr expression ∈ arguments → ∀ initial upper,
      ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets expression initial upper := by
  cases arguments with
  | nil => simp
  | cons first rest =>
    intro expression member
    cases first with
    | text text =>
      exact source_printargs_occurrence_replay rest source validity bounded scopes expression (by simpa using member)
    | expr first =>
      rcases List.mem_cons.mp member with same | member
      · cases PrintArg.expr.inj same
        exact source_expression_occurrence_replay expression source validity bounded (SourceScopesWithin.append.mp scopes).1
      · exact source_printargs_occurrence_replay rest source validity bounded (SourceScopesWithin.append.mp scopes).2 expression member
termination_by sizeOf arguments

theorem source_statement_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (statement : Stmt)
    (source : SourceContextEnvironment typingEnv env context)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.stmtScopes none statement)) :
    ∀ loop scope initial upper,
      StatementOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets loop scope statement initial upper := by
  intro loop scope initial upper
  cases statement with
  | letS variableId expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact statementOccurrence_let source.tables source.contextOk
      (source_expression_occurrence_replay expression source validity bounded scopedBounds initial upper)
  | rebind variableId expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact statementOccurrence_rebind source.tables source.accepted source.implementationRow source.contextOk
      (source_expression_occurrence_replay expression source validity bounded scopedBounds initial upper)
  | expr expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact statementOccurrence_expression (source_expression_occurrence_replay expression source validity bounded scopedBounds initial upper)
  | assign owner expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    apply statement_occurrence_context_of_global
    exact statementOccurrence_assign origin loop scope source.tables source.parameters (referenceSlicePlaceOccurrence_of_context source)
      (source_place_occurrence_replay owner source validity bounded parts.1 initial upper)
      (fun provenance => source_expression_occurrence_replay expression source validity bounded parts.2 _ provenance)
  | assignOp op owner expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    apply statement_occurrence_context_of_global
    exact statementOccurrence_assignOp op origin loop scope source.tables source.parameters
      (source_place_occurrence_replay owner source validity bounded parts.1 initial upper)
      (fun provenance => source_expression_occurrence_replay expression source validity bounded parts.2 _ provenance)
  | assignWhole owner expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    apply statement_occurrence_context_of_global
    exact statementOccurrence_assignWhole origin loop scope source.tables source.parameters
      (source_place_occurrence_replay owner source validity bounded parts.1 initial upper)
      (fun provenance => source_expression_occurrence_replay expression source validity bounded parts.2 _ provenance)
  | append owner view origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    apply statement_occurrence_context_of_global
    exact statementOccurrence_append origin loop scope source.tables source.parameters
      (source_place_occurrence_replay owner source validity bounded parts.1 initial upper)
      (fun provenance => source_view_occurrence_replay view source validity bounded parts.2 _ provenance)
  | popN owner count origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    apply statement_occurrence_context_of_global
    exact statementOccurrence_popN origin loop scope source.tables source.parameters
      (source_place_occurrence_replay owner source validity bounded parts.1 initial upper)
      (fun provenance => source_expression_occurrence_replay count source validity bounded parts.2 _ provenance)
  | resize owner count fill origin =>
    cases fill with
    | none =>
      have scopedBounds := scopes
      simp only [Core.stmtScopes] at scopedBounds
      have parts := SourceScopesWithin.append.mp (SourceScopesWithin.append.mp scopedBounds).1
      apply statement_occurrence_context_of_global
      exact statementOccurrence_resizeWithoutFill origin loop scope source.tables source.parameters
        (source_place_occurrence_replay owner source validity bounded parts.1 initial upper)
        (fun provenance => source_expression_occurrence_replay count source validity bounded parts.2 _ provenance)
    | some fill =>
      have scopedBounds := scopes
      simp only [Core.stmtScopes] at scopedBounds
      have parts := SourceScopesWithin.append.mp scopedBounds
      have first := SourceScopesWithin.append.mp parts.1
      apply statement_occurrence_context_of_global
      exact statementOccurrence_resizeWithFill origin loop scope source.tables source.readable source.parameters
        (source_place_occurrence_replay owner source validity bounded first.1 initial upper)
        (fun provenance => source_expression_occurrence_replay count source validity bounded first.2 _ provenance)
        (fun provenance => source_expression_occurrence_replay fill source validity bounded parts.2 _ provenance)
  | clear owner origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    apply statement_occurrence_context_of_global
    exact statementOccurrence_clear origin loop scope source.tables source.parameters
      (source_place_occurrence_replay owner source validity bounded scopedBounds initial upper)
  | ifS condition yes no origin =>
    cases no with
    | none =>
      have scopedBounds := scopes
      simp only [Core.stmtScopes, List.append_nil] at scopedBounds
      have parts := SourceScopesWithin.append.mp scopedBounds
      apply statementOccurrence_if (source_expression_occurrence_replay condition source validity bounded parts.1 initial upper)
      intro body member targets state provenance
      rcases member with same | impossible
      · subst body
        exact source_block_occurrence_replay (siteTargets := targets) yes source validity bounded parts.2 loop [] false state provenance
      · cases impossible
    | some no =>
      have scopedBounds := scopes
      simp only [Core.stmtScopes] at scopedBounds
      have parts := SourceScopesWithin.append.mp scopedBounds
      have first := SourceScopesWithin.append.mp parts.1
      apply statementOccurrence_if (source_expression_occurrence_replay condition source validity bounded first.1 initial upper)
      intro body member targets state provenance
      rcases member with same | same
      · subst body
        exact source_block_occurrence_replay (siteTargets := targets) yes source validity bounded first.2 loop [] false state provenance
      · have identity : body = no := (Option.some.inj same).symm
        subst body
        exact source_block_occurrence_replay (siteTargets := targets) no source validity bounded parts.2 loop [] false state provenance
  | «while» condition body origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    apply statementOccurrence_while
    · intro targets
      exact source_expression_occurrence_replay (siteTargets := targets) condition source validity bounded parts.1 _ upper
    · intro targets provenance
      exact source_block_occurrence_replay (siteTargets := targets) body (source.typingTables (nextEnv := { typingEnv with loops := typingEnv.loops + 1 }) rfl rfl rfl) validity bounded parts.2 _ [] false _ provenance
  | forRange variableId low high body origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    have first := SourceScopesWithin.append.mp parts.1
    apply statementOccurrence_range source.tables
      (source_expression_occurrence_replay low source validity bounded first.1 initial upper)
      (fun provenance => source_expression_occurrence_replay high source validity bounded first.2 _ provenance)
    intro targets depth header exit type counter state provenance
    dsimp only
    intro typeEq headerEq counterEq stateEq
    exact source_block_occurrence_replay (siteTargets := targets) body (source.typingTables (nextEnv := { typingEnv with loops := typingEnv.loops + 1, visible := variableId :: typingEnv.visible }) rfl rfl rfl) validity bounded parts.2 _ _ false state provenance
  | forEach variableId index view byRef body origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    apply statementOccurrence_each source.readable source.tables source.contextOk.annotationShape source.parameters
    · intro place same
      cases same
      exact source_place_occurrence_replay place source validity bounded parts.1 initial upper
    · intro expression same
      cases same
      exact source_expression_occurrence_replay expression source validity bounded parts.1 initial upper
    · intro targets depth header exit counter value state provenance
      dsimp only
      intro headerEq counterEq valueEq stateEq
      exact source_block_occurrence_replay (siteTargets := targets) body (source.typingTables (nextEnv := { typingEnv with loops := typingEnv.loops + 1, visible := variableId :: index.toList ++ typingEnv.visible }) rfl rfl rfl) validity bounded parts.2 _ _ false state provenance
  | ret expression origin =>
    cases expression with
    | none => exact statementOccurrence_returnUnit source.tables
    | some expression =>
        have scopedBounds := scopes
        simp only [Core.stmtScopes] at scopedBounds
        exact statementOccurrence_return source.tables source.implementation source.implementationRow source.contextOk
          (source_expression_occurrence_replay expression source validity bounded scopedBounds initial upper)
  | brk origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact statementOccurrence_break
  | cont origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact statementOccurrence_continue
  | print arguments origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    apply statement_occurrence_context_of_global
    exact statementOccurrence_print source.tables (source_printargs_occurrence_replay arguments source validity bounded scopedBounds)
  | assertS expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact statementOccurrence_assert origin source.tables (source_expression_occurrence_replay expression source validity bounded scopedBounds initial upper)
  | abort message origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact statementOccurrence_abort message origin source.tables
  | exit expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact statementOccurrence_exit origin source.tables (source_expression_occurrence_replay expression source validity bounded scopedBounds initial upper)
termination_by sizeOf statement

end

#print axioms source_expression_occurrence_replay
#print axioms source_place_occurrence_replay
#print axioms source_view_occurrence_replay
#print axioms source_bound_occurrence_replay
#print axioms source_block_occurrence_replay
#print axioms source_statements_occurrence_replay
#print axioms source_statement_occurrence_replay
#print axioms source_expressions_occurrence_replay
#print axioms source_arguments_occurrence_replay
#print axioms source_printargs_occurrence_replay

end Goose.Lower.Validation.ReplacementContentFlowSource
