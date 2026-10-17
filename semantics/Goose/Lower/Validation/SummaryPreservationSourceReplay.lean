import Goose.Lower.Validation.SummaryPreservationSourceContextEnvironment
import Goose.Lower.Validation.SummaryPreservationSourceExpressionKernels
import Goose.Lower.Validation.SummaryPreservationSourceScalarKernels
import Goose.Lower.Validation.SummaryPreservationSourceSliceKernels
import Goose.Lower.Validation.SummaryPreservationSourceCallKernels
import Goose.Lower.Validation.SummaryPreservationSourceExpressionControl
import Goose.Lower.Validation.SummaryPreservationSourceBlockKernels
import Goose.Lower.Validation.SummaryPreservationSourceStatementsKernels
import Goose.Lower.Validation.SummaryPreservationSourceReturnKernels
import Goose.Lower.Validation.SummaryPreservationSourceAbortKernels
import Goose.Lower.Validation.SummaryPreservationReplayNativeAggregates
import Goose.Lower.Validation.SummaryPreservationReplayTypedPlaces
import Goose.Lower.Validation.SummaryPreservationReplayTypedViews
import Goose.Lower.Validation.SummaryPreservationSourceMutationKernels
import Goose.Lower.Validation.SummaryPreservationSourceControlKernelsIf
import Goose.Lower.Validation.SummaryPreservationSourceControlKernelsLet
import Goose.Lower.Validation.SummaryPreservationSourceControlKernelsRebind
import Goose.Lower.Validation.SummaryPreservationSourceControlKernelsPrint
import Goose.Lower.Validation.SummaryPreservationReplayNativeLoopsEach
import Goose.Lower.Validation.SummaryPreservationReplayNativeLoopsRange
import Goose.Lower.Validation.SummaryPreservationReplayNativeLoopsWhile

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

variable {typingEnv : TEnv} {env : PEnv} {context : ContextId}
  {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat}

set_option maxHeartbeats 1200000

mutual

theorem source_expression_replay {typingEnv : TEnv} {env : PEnv} (expression : Expr)
    (source : SourceContextEnvironment typingEnv env context)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.exprScopes none expression)) :
    ∀ initial upper, ExpressionReplayAt typingEnv env results vt target scopeCount expression initial upper := by
  intro initial upper
  cases expression with
  | lit integer value =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact expressionReplay_literal integer value
  | bool value =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact expressionReplay_boolean value
  | read place =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact expressionReplay_read source.readable source.tables source.contextRow source.implementationRow
      (source_place_replay place source bounded scopedBounds initial upper)
  | ref mutability place =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact expressionReplay_reference mutability (source_place_replay place source bounded scopedBounds initial upper)
  | slice mutability view low high origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    have first := SourceScopesWithin.append.mp parts.1
    exact expressionReplay_slice mutability origin source.tables
      (source_view_replay view source bounded first.1 initial upper)
      (fun provenance => source_bound_replay low source bounded first.2 _ provenance)
      (fun provenance => source_bound_replay high source bounded parts.2 _ provenance)
  | len view =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact expressionReplay_length (source_view_replay view source bounded scopedBounds initial upper)
  | un op operand origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact expressionReplay_unary op origin source.tables (source_expression_replay operand source bounded scopedBounds initial upper)
  | bin op left right origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact expressionReplay_binary op origin source.tables
      (source_expression_replay left source bounded parts.1 initial upper)
      (fun provenance => source_expression_replay right source bounded parts.2 _ provenance)
  | cmp op left right =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact expressionReplay_comparison op
      (source_expression_replay left source bounded parts.1 initial upper)
      (fun provenance => source_expression_replay right source bounded parts.2 _ provenance)
  | and left right =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact expressionReplay_shortCircuit true
      (source_expression_replay left source bounded parts.1 initial upper)
      (fun provenance => source_expression_replay right source bounded parts.2 _ provenance)
  | or left right =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact expressionReplay_shortCircuit false
      (source_expression_replay left source bounded parts.1 initial upper)
      (fun provenance => source_expression_replay right source bounded parts.2 _ provenance)
  | not operand =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact expressionReplay_not (source_expression_replay operand source bounded scopedBounds initial upper)
  | conv kind destination operand origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact expressionReplay_conversion kind destination origin source.tables
      (source_expression_replay operand source bounded scopedBounds initial upper)
  | call callee args origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    apply expressionReplay_call source.tables source.accepted source.parameters bounded
    · intro operand member state provenance
      exact source_arguments_replay args source bounded scopedBounds (.byVal operand) member state provenance
    · intro mutability place member state provenance
      exact source_arguments_replay args source bounded scopedBounds (.byRef mutability place) member state provenance
  | push owner operand origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact expressionReplay_push origin source.tables source.accepted source.contextRow source.implementationRow
      (source_place_replay owner source bounded parts.1 initial upper)
      (fun provenance => source_expression_replay operand source bounded parts.2 _ provenance)
  | pop owner origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact expressionReplay_pop origin source.tables source.accepted source.contextRow source.implementationRow
      (source_place_replay owner source bounded scopedBounds initial upper)
  | ifE condition yes no =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    have first := SourceScopesWithin.append.mp parts.1
    apply expressionReplay_if first.2 parts.2
      (source_expression_replay condition source bounded first.1 initial upper)
    intro body member state provenance
    rcases member with rfl | rfl
    · exact source_block_replay body source.expression bounded first.2 _ _ _ state provenance
    · exact source_block_replay body source.expression bounded parts.2 _ _ _ state provenance
  | blockE body =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact expressionReplay_block scopedBounds (source_block_replay body source.expression bounded scopedBounds _ _ _ initial upper)
  | arrLit type elements =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    apply expressionReplay_arrayLiteral
    intro earlier operand later same provenance
    exact source_expressions_replay elements source bounded scopedBounds operand
      (by rw [same]; exact List.mem_append_right earlier (by simp)) _ provenance
  | structLit type elements =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    apply expressionReplay_structLiteral
    intro earlier operand later same provenance
    exact source_expressions_replay elements source bounded scopedBounds operand
      (by rw [same]; exact List.mem_append_right earlier (by simp)) _ provenance
  | fill type operand =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact expressionReplay_arrayFill (source_expression_replay operand source bounded scopedBounds initial upper)
termination_by sizeOf expression

theorem source_place_replay {typingEnv : TEnv} {env : PEnv} (place : Place)
    (source : SourceContextEnvironment typingEnv env context)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.placeScopes none place)) :
    ∀ initial upper, PlaceReplayAt typingEnv env results vt target scopeCount place initial upper := by
  intro initial upper info start finish before after roots typed replay ceiling ready generated native
  apply ReplayBuilder.typedPlace source.readable source.tables source.contextRow source.implementationRow
    typed replay ceiling ready generated native
  · intro owner field same
    cases same
    exact source_place_replay owner source bounded scopes initial upper
  · intro view index origin same
    cases same
    exact source_view_replay view source bounded (SourceScopesWithin.append.mp scopes).1 initial upper
  · intro expression state provenance occurrence
    rcases occurrence with ⟨rfl, rfl⟩ | ⟨view, origin, rfl, rfl⟩
    · exact source_expression_replay expression source bounded scopes state provenance
    · exact source_expression_replay expression source bounded (SourceScopesWithin.append.mp scopes).2 _ provenance
termination_by sizeOf place

theorem source_view_replay {typingEnv : TEnv} {env : PEnv} (view : View)
    (source : SourceContextEnvironment typingEnv env context)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.viewScopes none view)) :
    ∀ initial upper, ViewReplayAt typingEnv env results vt target scopeCount view initial upper := by
  intro initial upper info start finish before after roots typed replay ceiling ready generated native
  apply ReplayBuilder.typedView typed replay ceiling source.parameters ready generated native
  · intro place same
    cases same
    exact source_place_replay place source bounded scopes initial upper
  · intro expression same
    cases same
    exact source_expression_replay expression source bounded scopes initial upper
termination_by sizeOf view

theorem source_bound_replay {typingEnv : TEnv} {env : PEnv} (bound : Bound)
    (source : SourceContextEnvironment typingEnv env context)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.boundScopes none bound)) :
    ∀ initial upper, BoundReplayAt typingEnv env results vt target scopeCount bound initial upper := by
  intro initial upper
  apply boundReplay_of_expression
  intro expression occurrence
  rcases occurrence with rfl | rfl
  all_goals exact source_expression_replay expression source bounded scopes initial upper
termination_by sizeOf bound

theorem source_expressions_replay {typingEnv : TEnv} {env : PEnv} (expressions : List Expr)
    (source : SourceContextEnvironment typingEnv env context)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.exprsScopes none expressions)) :
    ∀ expression ∈ expressions, ∀ initial upper,
      ExpressionReplayAt typingEnv env results vt target scopeCount expression initial upper := by
  cases expressions with
  | nil => simp
  | cons first rest =>
    intro expression member
    rcases List.mem_cons.mp member with rfl | member
    · exact source_expression_replay expression source bounded (SourceScopesWithin.append.mp scopes).1
    · exact source_expressions_replay rest source bounded (SourceScopesWithin.append.mp scopes).2 expression member
termination_by sizeOf expressions
decreasing_by
  all_goals try decreasing_trivial
  all_goals try subst expressions
  all_goals try subst expression
  all_goals simp +arith

theorem source_arguments_replay {typingEnv : TEnv} {env : PEnv} (arguments : List Arg)
    (source : SourceContextEnvironment typingEnv env context)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.argsScopes none arguments)) :
    ∀ argument ∈ arguments, ∀ initial upper,
      match argument with
      | .byVal expression => ExpressionReplayAt typingEnv env results vt target scopeCount expression initial upper
      | .byRef _ place => PlaceReplayAt typingEnv env results vt target scopeCount place initial upper := by
  cases arguments with
  | nil => simp
  | cons first rest =>
    intro argument member
    rcases List.mem_cons.mp member with same | restMember
    · subst argument
      cases first with
      | byVal expression => exact source_expression_replay expression source bounded (SourceScopesWithin.append.mp scopes).1
      | byRef mutability place => exact source_place_replay place source bounded (SourceScopesWithin.append.mp scopes).1
    · cases first with
      | byVal expression => exact source_arguments_replay rest source bounded (SourceScopesWithin.append.mp scopes).2 argument restMember
      | byRef mutability place => exact source_arguments_replay rest source bounded (SourceScopesWithin.append.mp scopes).2 argument restMember
termination_by sizeOf arguments

theorem source_block_replay {typingEnv : TEnv} {env : PEnv} (body : Core.Block)
    (source : SourceContextEnvironment typingEnv env context)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.blockScopes none body)) :
    ∀ loop bindings want initial upper,
      BlockReplayAt typingEnv env results vt target scopeCount loop bindings want body initial upper := by
  intro loop bindings want initial upper
  cases body with
  | mk scope statements value =>
    apply blockReplay_of_children
    · intro nextEnv moduleEq variablesEq implEq modeEq state provenance
      exact source_statements_replay statements
        ((source.typingTables moduleEq variablesEq implEq).scopes (scope :: env.scopes)) bounded
        ((SourceScopesWithin.statements_parent statements (some scope) none).mp
          (SourceScopesWithin.block_parts scopes).2.1) loop scope state provenance
    · intro expression present expressionScopes nextEnv moduleEq variablesEq implEq modeEq state provenance
      exact source_expression_replay expression
        ((source.typingTables moduleEq variablesEq implEq).scopes (scope :: env.scopes)) bounded expressionScopes state provenance
termination_by sizeOf body

theorem source_statements_replay {typingEnv : TEnv} {env : PEnv} (statements : List Stmt)
    (source : SourceContextEnvironment typingEnv env context)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.stmtsScopes none statements)) :
    ∀ loop scope initial upper,
      StatementsReplayAt typingEnv env results vt target scopeCount loop scope statements initial upper := by
  intro loop scope initial upper
  apply statementsReplay_of_statement
  intro statement member nextEnv moduleEq variablesEq implEq modeEq state provenance
  exact source_statement_replay statement (source.typingTables moduleEq variablesEq implEq) bounded
    (SourceScopesWithin.stmts_member scopes member) loop scope state provenance
termination_by sizeOf statements

theorem source_printargs_replay {typingEnv : TEnv} {env : PEnv} (arguments : List PrintArg)
    (source : SourceContextEnvironment typingEnv env context)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.printScopes none arguments)) :
    ∀ expression, PrintArg.expr expression ∈ arguments → ∀ initial upper,
      ExpressionReplayAt typingEnv env results vt target scopeCount expression initial upper := by
  cases arguments with
  | nil => simp
  | cons first rest =>
    intro expression member
    cases first with
    | text text =>
      exact source_printargs_replay rest source bounded scopes expression (by simpa using member)
    | expr first =>
      rcases List.mem_cons.mp member with same | member
      · cases PrintArg.expr.inj same
        exact source_expression_replay expression source bounded (SourceScopesWithin.append.mp scopes).1
      · exact source_printargs_replay rest source bounded (SourceScopesWithin.append.mp scopes).2 expression member
termination_by sizeOf arguments

theorem source_statement_replay {typingEnv : TEnv} {env : PEnv} (statement : Stmt)
    (source : SourceContextEnvironment typingEnv env context)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.stmtScopes none statement)) :
    ∀ loop scope initial upper,
      StatementReplayAt typingEnv env results vt target scopeCount loop scope statement initial upper := by
  intro loop scope initial upper
  cases statement with
  | letS variableId expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact statementReplay_let source.tables source.contextOk
      (source_expression_replay expression source bounded scopedBounds initial upper)
  | rebind variableId expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact statementReplay_rebind source.tables source.accepted source.implementationRow source.contextOk
      (source_expression_replay expression source bounded scopedBounds initial upper)
  | expr expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact statementReplay_expression (source_expression_replay expression source bounded scopedBounds initial upper)
  | assign owner expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact statementReplay_assign origin loop scope source.tables source.accepted source.contextRow source.implementationRow
      (source_place_replay owner source bounded parts.1 initial upper)
      (fun provenance => source_expression_replay expression source bounded parts.2 _ provenance)
  | assignOp op owner expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact statementReplay_assignOp op origin loop scope source.tables source.accepted source.contextRow source.implementationRow
      (source_place_replay owner source bounded parts.1 initial upper)
      (fun provenance => source_expression_replay expression source bounded parts.2 _ provenance)
  | assignWhole owner expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact statementReplay_assignWhole origin loop scope source.tables source.accepted source.contextRow source.implementationRow
      (source_place_replay owner source bounded parts.1 initial upper)
      (fun provenance => source_expression_replay expression source bounded parts.2 _ provenance)
  | append owner view origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact statementReplay_append origin loop scope source.tables source.accepted source.contextRow source.implementationRow
      (source_place_replay owner source bounded parts.1 initial upper)
      (fun provenance => source_view_replay view source bounded parts.2 _ provenance)
  | popN owner count origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact statementReplay_popN origin loop scope source.tables source.accepted source.contextRow source.implementationRow
      (source_place_replay owner source bounded parts.1 initial upper)
      (fun provenance => source_expression_replay count source bounded parts.2 _ provenance)
  | resize owner count fill origin =>
    cases fill with
    | none =>
      have scopedBounds := scopes
      simp only [Core.stmtScopes] at scopedBounds
      have parts := SourceScopesWithin.append.mp (SourceScopesWithin.append.mp scopedBounds).1
      exact statementReplay_resizeWithoutFill origin loop scope source.tables source.accepted source.contextRow source.implementationRow
        (source_place_replay owner source bounded parts.1 initial upper)
        (fun provenance => source_expression_replay count source bounded parts.2 _ provenance)
    | some fill =>
      have scopedBounds := scopes
      simp only [Core.stmtScopes] at scopedBounds
      have parts := SourceScopesWithin.append.mp scopedBounds
      have first := SourceScopesWithin.append.mp parts.1
      exact statementReplay_resizeWithFill origin loop scope source.tables source.accepted source.contextRow source.implementationRow
        (source_place_replay owner source bounded first.1 initial upper)
        (fun provenance => source_expression_replay count source bounded first.2 _ provenance)
        (fun provenance => source_expression_replay fill source bounded parts.2 _ provenance)
  | clear owner origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact statementReplay_clear origin loop scope source.tables source.accepted source.contextRow source.implementationRow
      (source_place_replay owner source bounded scopedBounds initial upper)
  | ifS condition yes no origin =>
    cases no with
    | none =>
      have scopedBounds := scopes
      simp only [Core.stmtScopes, List.append_nil] at scopedBounds
      have parts := SourceScopesWithin.append.mp scopedBounds
      apply statementReplay_if (source_expression_replay condition source bounded parts.1 initial upper)
      intro body member state provenance
      rcases member with same | impossible
      · subst body
        exact source_block_replay yes source bounded parts.2 loop [] false state provenance
      · cases impossible
    | some no =>
      have scopedBounds := scopes
      simp only [Core.stmtScopes] at scopedBounds
      have parts := SourceScopesWithin.append.mp scopedBounds
      have first := SourceScopesWithin.append.mp parts.1
      apply statementReplay_if (source_expression_replay condition source bounded first.1 initial upper)
      intro body member state provenance
      rcases member with same | same
      · subst body
        exact source_block_replay yes source bounded first.2 loop [] false state provenance
      · have identity : body = no := (Option.some.inj same).symm
        subst body
        exact source_block_replay no source bounded parts.2 loop [] false state provenance
  | «while» condition body origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    intro output start finish before after typed replay ceiling _scopes stack ready generated loopTargets loopReplay native
    have parts := SourceScopesWithin.append.mp scopedBounds
    apply ready.typedWhileNative loop typed replay ceiling parts.2 stack generated native
      (source_expression_replay condition source bounded parts.1 _ upper)
    intro provenance
    exact source_block_replay body (source.typingTables (nextEnv := { typingEnv with loops := typingEnv.loops + 1 }) rfl rfl rfl) bounded parts.2 _ [] false _ provenance
  | forRange variableId low high body origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    intro output start finish before after typed replay ceiling _scopes stack ready generated loopTargets loopReplay native
    have parts := SourceScopesWithin.append.mp scopedBounds
    have first := SourceScopesWithin.append.mp parts.1
    apply ready.typedRangeNative loop source.tables typed replay ceiling parts.2 stack generated native
      (source_expression_replay low source bounded first.1 initial upper)
      (fun provenance => source_expression_replay high source bounded first.2 _ provenance)
    intro depth header exit type counter state provenance
    dsimp only
    intro typeEq headerEq counterEq stateEq
    exact source_block_replay body (source.typingTables (nextEnv := { typingEnv with loops := typingEnv.loops + 1, visible := variableId :: typingEnv.visible }) rfl rfl rfl) bounded parts.2 _ _ false state provenance
  | forEach variableId index view byRef body origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    intro output start finish before after typed replay ceiling _scopes stack ready generated loopTargets loopReplay native
    have parts := SourceScopesWithin.append.mp scopedBounds
    apply ready.typedEachNative loop source.readable source.tables source.contextOk.annotationShape
      typed replay ceiling parts.2 stack source.parameters generated native
    · intro place same
      cases same
      exact source_place_replay place source bounded parts.1 initial upper
    · intro expression same
      cases same
      exact source_expression_replay expression source bounded parts.1 initial upper
    · intro depth header exit counter value state provenance
      dsimp only
      intro headerEq counterEq valueEq stateEq
      exact source_block_replay body (source.typingTables (nextEnv := { typingEnv with loops := typingEnv.loops + 1, visible := variableId :: index.toList ++ typingEnv.visible }) rfl rfl rfl) bounded parts.2 _ _ false state provenance
  | ret expression origin =>
    cases expression with
    | none => exact statementReplay_returnUnit source.tables
    | some expression =>
        have scopedBounds := scopes
        simp only [Core.stmtScopes] at scopedBounds
        exact statementReplay_return source.tables source.implementation source.implementationRow source.contextOk
          (source_expression_replay expression source bounded scopedBounds initial upper)
  | brk origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact statementReplay_break
  | cont origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact statementReplay_continue
  | print arguments origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact statementReplay_print source.tables (source_printargs_replay arguments source bounded scopedBounds)
  | assertS expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact statementReplay_assert origin source.tables (source_expression_replay expression source bounded scopedBounds initial upper)
  | abort message origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact statementReplay_abort message origin source.tables
  | exit expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact statementReplay_exit origin source.tables (source_expression_replay expression source bounded scopedBounds initial upper)
termination_by sizeOf statement

end

#print axioms source_expression_replay
#print axioms source_place_replay
#print axioms source_view_replay
#print axioms source_bound_replay
#print axioms source_block_replay
#print axioms source_statements_replay
#print axioms source_statement_replay
#print axioms source_expressions_replay
#print axioms source_arguments_replay
#print axioms source_printargs_replay

end Goose.Lower.Validation.SummaryPreservation
