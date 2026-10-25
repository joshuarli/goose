import Goose.Lower.Validation.SourceCanonicalRootFloorsWriteLookup
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceScalarsGlobal
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAggregatesGlobal
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessGlobalRead
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessGlobalReference
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessGlobalSlice
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessGlobalLength
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessGlobalBounds
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrencePlacesGlobal
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceViewsGlobal
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceCallsGlobalEmpty
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceStorage
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlGlobalStatements
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlGlobalBlocks
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlGlobalIf
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlGlobalWhile
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlGlobalIfExpression
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlGlobalShortCircuit
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlGlobalBlockExpression
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlGlobalAbort
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlGlobalTransfers
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlGlobalExpressionStatement
import Goose.Lower.Validation.SummaryPreservationSourceGlobalEnvironment
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)}
  {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId}

set_option maxHeartbeats 1200000

mutual

theorem global_source_expression_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (expression : Expr)
    (source : SourceGlobalEnvironment typingEnv env func)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.exprScopes none expression)) :
    ∀ initial upper, GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets expression initial upper := by
  intro initial upper
  cases expression with
  | lit integer value =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact globalExpressionOccurrence_literal integer value
  | bool value =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact globalExpressionOccurrence_boolean value
  | read place =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact occurrenceReplay_global_read source.readable source.tables source.variables source.parameters
      (global_source_place_occurrence_replay place source validity bounded scopedBounds) initial upper
  | ref mutability place =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact occurrenceReplay_global_reference mutability source.tables (global_source_place_occurrence_replay place source validity bounded scopedBounds) initial upper
  | slice mutability view low high origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    have first := SourceScopesWithin.append.mp parts.1
    exact occurrenceReplay_global_slice mutability origin source.tables
      (global_source_view_occurrence_replay view source validity bounded first.1)
      (global_source_bound_occurrence_replay low source validity bounded first.2)
      (global_source_bound_occurrence_replay high source validity bounded parts.2) initial upper
  | len view =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact occurrenceReplay_global_length source.tables (global_source_view_occurrence_replay view source validity bounded scopedBounds) initial upper
  | un op operand origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact globalExpressionOccurrence_unary op origin source.tables (global_source_expression_occurrence_replay operand source validity bounded scopedBounds initial upper)
  | bin op left right origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact globalExpressionOccurrence_binary op origin source.tables
      (global_source_expression_occurrence_replay left source validity bounded parts.1 initial upper)
      (fun provenance => global_source_expression_occurrence_replay right source validity bounded parts.2 _ provenance)
  | cmp op left right =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact globalExpressionOccurrence_comparison op source.tables
      (global_source_expression_occurrence_replay left source validity bounded parts.1 initial upper)
      (fun provenance => global_source_expression_occurrence_replay right source validity bounded parts.2 _ provenance)
  | and left right =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact globalExpressionOccurrence_shortCircuit true
      (global_source_expression_occurrence_replay left source validity bounded parts.1 initial upper)
      (fun targets provenance => global_source_expression_occurrence_replay (siteTargets := targets) right source validity bounded parts.2 _ provenance)
  | or left right =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact globalExpressionOccurrence_shortCircuit false
      (global_source_expression_occurrence_replay left source validity bounded parts.1 initial upper)
      (fun targets provenance => global_source_expression_occurrence_replay (siteTargets := targets) right source validity bounded parts.2 _ provenance)
  | not operand =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact globalExpressionOccurrence_not source.tables (global_source_expression_occurrence_replay operand source validity bounded scopedBounds initial upper)
  | conv kind destination operand origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact globalExpressionOccurrence_conversion kind destination origin source.tables
      (global_source_expression_occurrence_replay operand source validity bounded scopedBounds initial upper)
  | call callee args origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    apply globalExpressionOccurrence_call_empty source.tables source.variables source.accepted source.parameters validity bounded
    · intro operand member state provenance
      exact global_source_arguments_occurrence_replay args source validity bounded scopedBounds (.byVal operand) member state provenance
    · intro mutability place member state provenance
      exact global_source_arguments_occurrence_replay args source validity bounded scopedBounds (.byRef mutability place) member state provenance
  | push owner operand origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact expressionOccurrence_push origin source.tables source.readable source.parameters
      (global_source_place_occurrence_replay owner source validity bounded parts.1 initial upper)
      (fun provenance => global_source_expression_occurrence_replay operand source validity bounded parts.2 _ provenance)
  | pop owner origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact expressionOccurrence_pop origin source.tables source.parameters
      (global_source_place_occurrence_replay owner source validity bounded scopedBounds initial upper)
  | ifE condition yes no =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    have first := SourceScopesWithin.append.mp parts.1
    apply globalExpressionOccurrence_if source.tables source.noParameters source.parameterIdentity validity first.2 parts.2
      (global_source_expression_occurrence_replay condition source validity bounded first.1 initial upper)
    intro body occurrence state provenance
    rcases occurrence with rfl | rfl
    · exact global_source_block_occurrence_replay body source.expression validity bounded first.2 _ _ _ _ provenance
    · exact global_source_block_occurrence_replay body source.expression validity bounded parts.2 _ _ _ _ provenance
  | blockE body =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact globalExpressionOccurrence_block scopedBounds (global_source_block_occurrence_replay body source.expression validity bounded scopedBounds _ _ _ initial upper)
  | arrLit type elements =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    apply globalExpressionOccurrence_arrayLiteral source.tables
    exact global_source_expressions_occurrence_replay elements source validity bounded scopedBounds
  | structLit type elements =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    apply globalExpressionOccurrence_structLiteral source.tables
    exact global_source_expressions_occurrence_replay elements source validity bounded scopedBounds
  | fill type operand =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact globalExpressionOccurrence_arrayFill source.tables (global_source_expression_occurrence_replay operand source validity bounded scopedBounds initial upper)
termination_by sizeOf expression

theorem global_source_place_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (place : Place)
    (source : SourceGlobalEnvironment typingEnv env func)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.placeScopes none place)) :
    ∀ initial upper, GlobalPlaceOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets place initial upper := by
  apply occurrenceReplay_global_place place source.tables source.variables
  · intro owner field same
    cases same
    exact global_source_place_occurrence_replay owner source validity bounded scopes
  · intro view index origin same
    cases same
    exact global_source_view_occurrence_replay view source validity bounded (SourceScopesWithin.append.mp scopes).1
  · intro expression state provenance occurrence
    rcases occurrence with rfl | ⟨view, origin, rfl⟩
    · exact global_source_expression_occurrence_replay expression source validity bounded scopes state provenance
    · exact global_source_expression_occurrence_replay expression source validity bounded (SourceScopesWithin.append.mp scopes).2 state provenance
termination_by sizeOf place

theorem global_source_view_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (view : View)
    (source : SourceGlobalEnvironment typingEnv env func)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.viewScopes none view)) :
    ∀ initial upper, GlobalViewOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets view initial upper := by
  apply occurrenceReplay_global_view view source.tables source.parameters
  · intro place same
    cases same
    exact global_source_place_occurrence_replay place source validity bounded scopes
  · intro expression same
    cases same
    exact global_source_expression_occurrence_replay expression source validity bounded scopes
termination_by sizeOf view

theorem global_source_bound_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (bound : Bound)
    (source : SourceGlobalEnvironment typingEnv env func)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.boundScopes none bound)) :
    ∀ initial upper, GlobalBoundOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets bound initial upper := by
  apply occurrenceReplay_global_bound bound source.tables
  intro expression occurrence
  rcases occurrence with rfl | rfl
  all_goals exact global_source_expression_occurrence_replay expression source validity bounded scopes
termination_by sizeOf bound

theorem global_source_expressions_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (expressions : List Expr)
    (source : SourceGlobalEnvironment typingEnv env func)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.exprsScopes none expressions)) :
    ∀ expression ∈ expressions, ∀ initial upper,
      GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets expression initial upper := by
  cases expressions with
  | nil => simp
  | cons first rest =>
    intro expression member
    rcases List.mem_cons.mp member with rfl | member
    · exact global_source_expression_occurrence_replay expression source validity bounded (SourceScopesWithin.append.mp scopes).1
    · exact global_source_expressions_occurrence_replay rest source validity bounded (SourceScopesWithin.append.mp scopes).2 expression member
termination_by sizeOf expressions
decreasing_by
  all_goals try decreasing_trivial
  all_goals try subst expressions
  all_goals try subst expression
  all_goals simp +arith

theorem global_source_arguments_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (arguments : List Arg)
    (source : SourceGlobalEnvironment typingEnv env func)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.argsScopes none arguments)) :
    ∀ argument ∈ arguments, ∀ initial upper,
      match argument with
      | .byVal expression => GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets expression initial upper
      | .byRef _ place => GlobalPlaceOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets place initial upper := by
  cases arguments with
  | nil => simp
  | cons first rest =>
    intro argument member
    rcases List.mem_cons.mp member with same | restMember
    · subst argument
      cases first with
      | byVal expression => exact global_source_expression_occurrence_replay expression source validity bounded (SourceScopesWithin.append.mp scopes).1
      | byRef mutability place => exact global_source_place_occurrence_replay place source validity bounded (SourceScopesWithin.append.mp scopes).1
    · cases first with
      | byVal expression => exact global_source_arguments_occurrence_replay rest source validity bounded (SourceScopesWithin.append.mp scopes).2 argument restMember
      | byRef mutability place => exact global_source_arguments_occurrence_replay rest source validity bounded (SourceScopesWithin.append.mp scopes).2 argument restMember
termination_by sizeOf arguments

theorem global_source_block_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (body : Core.Block)
    (source : SourceGlobalEnvironment typingEnv env func)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.blockScopes none body)) :
    ∀ loop bindings want initial upper,
      GlobalBlockOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets loop bindings want body initial upper := by
  intro loop bindings want initial upper
  cases body with
  | mk scope statements value =>
    apply globalBlockOccurrence_of_children source.inside
    · intro nextEnv moduleEq variablesEq implEq modeEq state provenance
      exact global_source_statements_occurrence_replay statements
        ((source.typingTables moduleEq variablesEq modeEq).scopes (scope :: env.scopes)) validity bounded
        ((SourceScopesWithin.statements_parent statements (some scope) none).mp
          (SourceScopesWithin.block_parts scopes).2.1) loop (.block (.mk scope statements value)) scope state provenance
    · intro expression present expressionScopes nextEnv moduleEq variablesEq implEq modeEq state provenance
      exact global_source_expression_occurrence_replay expression
        ((source.typingTables moduleEq variablesEq modeEq).scopes (scope :: env.scopes)) validity bounded expressionScopes state provenance
termination_by sizeOf body

theorem global_source_statements_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (statements : List Stmt)
    (source : SourceGlobalEnvironment typingEnv env func)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.stmtsScopes none statements)) :
    ∀ loop root scope initial upper,
      GlobalStatementsOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets loop root scope statements initial upper := by
  intro loop root scope initial upper
  apply globalStatementsOccurrence_of_statement
  intro statement member nextEnv moduleEq variablesEq implEq modeEq state provenance
  exact global_source_statement_occurrence_replay statement (source.typingTables moduleEq variablesEq modeEq) validity bounded
    (SourceScopesWithin.stmts_member scopes member) loop scope state provenance
termination_by sizeOf statements

theorem global_source_printargs_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (arguments : List PrintArg)
    (source : SourceGlobalEnvironment typingEnv env func)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.printScopes none arguments)) :
    ∀ expression, PrintArg.expr expression ∈ arguments → ∀ initial upper,
      GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets expression initial upper := by
  cases arguments with
  | nil => simp
  | cons first rest =>
    intro expression member
    cases first with
    | text text =>
      exact global_source_printargs_occurrence_replay rest source validity bounded scopes expression (by simpa using member)
    | expr first =>
      rcases List.mem_cons.mp member with same | member
      · cases PrintArg.expr.inj same
        exact global_source_expression_occurrence_replay expression source validity bounded (SourceScopesWithin.append.mp scopes).1
      · exact global_source_printargs_occurrence_replay rest source validity bounded (SourceScopesWithin.append.mp scopes).2 expression member
termination_by sizeOf arguments

theorem global_source_statement_occurrence_replay {typingEnv : TEnv} {env : PEnv} {siteTargets : List BlockId} (statement : Stmt)
    (source : SourceGlobalEnvironment typingEnv env func)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.stmtScopes none statement)) :
    ∀ loop scope initial upper,
      GlobalStatementOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets loop scope statement initial upper := by
  intro loop scope initial upper
  cases statement with
  | letS variableId expression origin => exact statementOccurrence_let_global source.variables
  | rebind variableId expression origin => exact statementOccurrence_rebind_global source.variables
  | expr expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact globalStatementOccurrence_expression (global_source_expression_occurrence_replay expression source validity bounded scopedBounds initial upper)
  | assign owner expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact statementOccurrence_assign origin loop scope source.tables source.parameters (referenceSlicePlaceOccurrence_of_empty_variables (source.tables.variablesEq.trans source.variables))
      (global_source_place_occurrence_replay owner source validity bounded parts.1 initial upper)
      (fun provenance => global_source_expression_occurrence_replay expression source validity bounded parts.2 _ provenance)
  | assignOp op owner expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact statementOccurrence_assignOp op origin loop scope source.tables source.parameters
      (global_source_place_occurrence_replay owner source validity bounded parts.1 initial upper)
      (fun provenance => global_source_expression_occurrence_replay expression source validity bounded parts.2 _ provenance)
  | assignWhole owner expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact statementOccurrence_assignWhole origin loop scope source.tables source.parameters
      (global_source_place_occurrence_replay owner source validity bounded parts.1 initial upper)
      (fun provenance => global_source_expression_occurrence_replay expression source validity bounded parts.2 _ provenance)
  | append owner view origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact statementOccurrence_append origin loop scope source.tables source.parameters
      (global_source_place_occurrence_replay owner source validity bounded parts.1 initial upper)
      (fun provenance => global_source_view_occurrence_replay view source validity bounded parts.2 _ provenance)
  | popN owner count origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact statementOccurrence_popN origin loop scope source.tables source.parameters
      (global_source_place_occurrence_replay owner source validity bounded parts.1 initial upper)
      (fun provenance => global_source_expression_occurrence_replay count source validity bounded parts.2 _ provenance)
  | resize owner count fill origin =>
    cases fill with
    | none =>
      have scopedBounds := scopes
      simp only [Core.stmtScopes] at scopedBounds
      have parts := SourceScopesWithin.append.mp (SourceScopesWithin.append.mp scopedBounds).1
      exact statementOccurrence_resizeWithoutFill origin loop scope source.tables source.parameters
        (global_source_place_occurrence_replay owner source validity bounded parts.1 initial upper)
        (fun provenance => global_source_expression_occurrence_replay count source validity bounded parts.2 _ provenance)
    | some fill =>
      have scopedBounds := scopes
      simp only [Core.stmtScopes] at scopedBounds
      have parts := SourceScopesWithin.append.mp scopedBounds
      have first := SourceScopesWithin.append.mp parts.1
      exact statementOccurrence_resizeWithFill origin loop scope source.tables source.readable source.parameters
        (global_source_place_occurrence_replay owner source validity bounded first.1 initial upper)
        (fun provenance => global_source_expression_occurrence_replay count source validity bounded first.2 _ provenance)
        (fun provenance => global_source_expression_occurrence_replay fill source validity bounded parts.2 _ provenance)
  | clear owner origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact statementOccurrence_clear origin loop scope source.tables source.parameters
      (global_source_place_occurrence_replay owner source validity bounded scopedBounds initial upper)
  | ifS condition yes no origin =>
    cases no with
    | none =>
      have scopedBounds := scopes
      simp only [Core.stmtScopes, List.append_nil] at scopedBounds
      have parts := SourceScopesWithin.append.mp scopedBounds
      apply globalStatementOccurrence_if source.inside (global_source_expression_occurrence_replay condition source validity bounded parts.1 initial upper)
      intro body member targets state provenance
      rcases member with same | impossible
      · subst body
        exact global_source_block_occurrence_replay (siteTargets := targets) yes source validity bounded parts.2 loop [] false state provenance
      · cases impossible
    | some no =>
      have scopedBounds := scopes
      simp only [Core.stmtScopes] at scopedBounds
      have parts := SourceScopesWithin.append.mp scopedBounds
      have first := SourceScopesWithin.append.mp parts.1
      apply globalStatementOccurrence_if source.inside (global_source_expression_occurrence_replay condition source validity bounded first.1 initial upper)
      intro body member targets state provenance
      rcases member with same | same
      · subst body
        exact global_source_block_occurrence_replay (siteTargets := targets) yes source validity bounded first.2 loop [] false state provenance
      · have identity : body = no := (Option.some.inj same).symm
        subst body
        exact global_source_block_occurrence_replay (siteTargets := targets) no source validity bounded parts.2 loop [] false state provenance
  | «while» condition body origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    apply globalStatementOccurrence_while source.inside
    · intro targets
      exact global_source_expression_occurrence_replay (siteTargets := targets) condition source validity bounded parts.1 _ upper
    · intro targets provenance
      exact global_source_block_occurrence_replay (siteTargets := targets) body (source.typingTables (nextEnv := {typingEnv with loops := typingEnv.loops + 1}) rfl rfl rfl) validity bounded parts.2 _ _ _ _ provenance
  | forRange variableId low high body origin =>
    intro location output start finish before after typed
    obtain ⟨localVar, integer, childStart, lowFinish, highFinish, bodyType, declared, _⟩ := tyStmt_forRange_children typed
    have row := (declare_ok _ _ _ _ _ declared).2.1
    simp [source.variables] at row
  | forEach variableId index view byRef body origin =>
    intro location output start finish before after typed
    obtain ⟨localVar, element, writable, indexStart, viewStart, viewFinish, bodyType, declared, _⟩ := tyStmt_forEach_children typed
    have row := (declare_ok _ _ _ _ _ declared).2.1
    simp [source.variables] at row
  | ret value origin =>
    cases value with
    | none => exact statementOccurrence_returnUnit_global source.inside
    | some expression => exact statementOccurrence_return_global source.inside
  | brk origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact globalStatementOccurrence_break
  | cont origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact globalStatementOccurrence_continue
  | print arguments origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact statementOccurrence_print source.tables (global_source_printargs_occurrence_replay arguments source validity bounded scopedBounds)
  | assertS expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact globalStatementOccurrence_assert origin source.tables (global_source_expression_occurrence_replay expression source validity bounded scopedBounds initial upper)
  | abort message origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact globalStatementOccurrence_abort message origin source.tables
  | exit expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact globalStatementOccurrence_exit origin source.tables (global_source_expression_occurrence_replay expression source validity bounded scopedBounds initial upper)
termination_by sizeOf statement

end

#print axioms global_source_expression_occurrence_replay
#print axioms global_source_place_occurrence_replay
#print axioms global_source_view_occurrence_replay
#print axioms global_source_bound_occurrence_replay
#print axioms global_source_block_occurrence_replay
#print axioms global_source_statements_occurrence_replay
#print axioms global_source_statement_occurrence_replay
#print axioms global_source_expressions_occurrence_replay
#print axioms global_source_arguments_occurrence_replay
#print axioms global_source_printargs_occurrence_replay

end Goose.Lower.Validation.ReplacementContentFlowSource
