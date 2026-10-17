import Goose.Lower.Validation.SourceGlobalExpression
import Goose.Lower.Validation.SourceGlobalControl

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

structure SourceGlobalEnvironment (typingEnv : TEnv) (env : PEnv) (func : Func) : Prop where
  accepted : Core.validate env.mod = .ok ()
  tables : SourceRootTables typingEnv env
  variables : typingEnv.vars = #[]
  inside : typingEnv.inExpr = true
  parameters : ParameterRootsClosed func

namespace SourceGlobalEnvironment

variable {typingEnv nextEnv : TEnv} {env : PEnv} {func : Func}

theorem readable (source : SourceGlobalEnvironment typingEnv env func) : SourceReadableEnvironment typingEnv :=
  SourceReadableEnvironment.empty (by simpa only [source.tables.moduleEq] using source.accepted) source.variables

theorem typingTables (source : SourceGlobalEnvironment typingEnv env func)
    (moduleEq : nextEnv.mod = typingEnv.mod) (variablesEq : nextEnv.vars = typingEnv.vars)
    (modeEq : nextEnv.inExpr = typingEnv.inExpr) : SourceGlobalEnvironment nextEnv env func :=
  ⟨source.accepted, ⟨source.tables.moduleEq.trans moduleEq.symm, source.tables.variablesEq.trans variablesEq.symm⟩,
    variablesEq.trans source.variables, modeEq.trans source.inside, source.parameters⟩

theorem expression (source : SourceGlobalEnvironment typingEnv env func) :
    SourceGlobalEnvironment (exprEnv typingEnv) env func :=
  ⟨source.accepted, ⟨source.tables.moduleEq, source.tables.variablesEq⟩, source.variables, rfl, source.parameters⟩

theorem scopes (source : SourceGlobalEnvironment typingEnv env func) (scopes : List ScopeId) :
    SourceGlobalEnvironment typingEnv {env with scopes := scopes} func :=
  ⟨source.accepted, ⟨source.tables.moduleEq, source.tables.variablesEq⟩, source.variables, source.inside, source.parameters⟩

end SourceGlobalEnvironment

variable {typingEnv : TEnv} {env : PEnv} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)}
  {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat}

set_option maxHeartbeats 1200000

mutual

theorem global_source_expression_replay {typingEnv : TEnv} {env : PEnv} (expression : Expr)
    (source : SourceGlobalEnvironment typingEnv env func)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.exprScopes none expression)) :
    ∀ initial upper, GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount expression initial upper := by
  intro initial upper
  cases expression with
  | lit integer value =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact globalExpressionReplay_literal integer value
  | bool value =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact globalExpressionReplay_boolean value
  | read place =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact globalExpressionReplay_read source.readable source.tables source.variables source.parameters
      (global_source_place_replay place source bounded scopedBounds initial upper)
  | ref mutability place =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact globalExpressionReplay_reference mutability (global_source_place_replay place source bounded scopedBounds initial upper)
  | slice mutability view low high origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    have first := SourceScopesWithin.append.mp parts.1
    exact globalExpressionReplay_slice mutability origin source.tables
      (global_source_view_replay view source bounded first.1 initial upper)
      (fun provenance => global_source_bound_replay low source bounded first.2 _ provenance)
      (fun provenance => global_source_bound_replay high source bounded parts.2 _ provenance)
  | len view =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact globalExpressionReplay_length (global_source_view_replay view source bounded scopedBounds initial upper)
  | un op operand origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact globalExpressionReplay_unary op origin source.tables (global_source_expression_replay operand source bounded scopedBounds initial upper)
  | bin op left right origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact globalExpressionReplay_binary op origin source.tables
      (global_source_expression_replay left source bounded parts.1 initial upper)
      (fun provenance => global_source_expression_replay right source bounded parts.2 _ provenance)
  | cmp op left right =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact globalExpressionReplay_comparison op
      (global_source_expression_replay left source bounded parts.1 initial upper)
      (fun provenance => global_source_expression_replay right source bounded parts.2 _ provenance)
  | and left right =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact globalExpressionReplay_shortCircuit true
      (global_source_expression_replay left source bounded parts.1 initial upper)
      (fun provenance => global_source_expression_replay right source bounded parts.2 _ provenance)
  | or left right =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact globalExpressionReplay_shortCircuit false
      (global_source_expression_replay left source bounded parts.1 initial upper)
      (fun provenance => global_source_expression_replay right source bounded parts.2 _ provenance)
  | not operand =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact globalExpressionReplay_not (global_source_expression_replay operand source bounded scopedBounds initial upper)
  | conv kind destination operand origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact globalExpressionReplay_conversion kind destination origin source.tables
      (global_source_expression_replay operand source bounded scopedBounds initial upper)
  | call callee args origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    apply globalExpressionReplay_call source.tables source.accepted source.parameters bounded
    · intro earlier operand suffix same provenance
      exact global_source_arguments_replay args source bounded scopedBounds (.byVal operand)
        (by rw [same]; simp) _ provenance
    · intro earlier mutability place suffix same provenance
      exact global_source_arguments_replay args source bounded scopedBounds (.byRef mutability place)
        (by rw [same]; simp) _ provenance
  | push owner operand origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact globalExpressionReplay_push origin source.tables source.parameters
      (global_source_place_replay owner source bounded parts.1 initial upper)
      (fun provenance => global_source_expression_replay operand source bounded parts.2 _ provenance)
  | pop owner origin =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact globalExpressionReplay_pop origin source.tables source.parameters
      (global_source_place_replay owner source bounded scopedBounds initial upper)
  | ifE condition yes no =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    have first := SourceScopesWithin.append.mp parts.1
    apply globalExpressionReplay_if first.2 parts.2
      (global_source_expression_replay condition source bounded first.1 initial upper)
    intro body state provenance occurrence
    rcases occurrence with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact global_source_block_replay body source.expression bounded first.2 _ _ _ _ provenance
    · exact global_source_block_replay body source.expression bounded parts.2 _ _ _ _ provenance
  | blockE body =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact globalExpressionReplay_block scopedBounds (global_source_block_replay body source.expression bounded scopedBounds _ _ _ initial upper)
  | arrLit type elements =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    apply globalExpressionReplay_arrayLiteral
    intro earlier operand later same provenance
    exact global_source_expressions_replay elements source bounded scopedBounds operand
      (by rw [same]; exact List.mem_append_right earlier (by simp)) _ provenance
  | structLit type elements =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    apply globalExpressionReplay_structLiteral
    intro earlier operand later same provenance
    exact global_source_expressions_replay elements source bounded scopedBounds operand
      (by rw [same]; exact List.mem_append_right earlier (by simp)) _ provenance
  | fill type operand =>
    have scopedBounds := scopes
    simp only [Core.exprScopes] at scopedBounds
    exact globalExpressionReplay_arrayFill (global_source_expression_replay operand source bounded scopedBounds initial upper)
termination_by sizeOf expression

theorem global_source_place_replay {typingEnv : TEnv} {env : PEnv} (place : Place)
    (source : SourceGlobalEnvironment typingEnv env func)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.placeScopes none place)) :
    ∀ initial upper, GlobalPlaceReplayAt typingEnv env results vt func returnTypes slots target scopeCount place initial upper := by
  intro initial upper info start finish before after roots typed replay ceiling ready generated native
  apply ReplayBuilder.typedGlobalPlace source.tables source.variables
    typed replay ceiling ready generated native
  · intro owner field same
    cases same
    exact global_source_place_replay owner source bounded scopes initial upper
  · intro view index origin same
    cases same
    exact global_source_view_replay view source bounded (SourceScopesWithin.append.mp scopes).1 initial upper
  · intro expression state provenance occurrence
    rcases occurrence with ⟨rfl, rfl⟩ | ⟨view, origin, rfl, rfl⟩
    · exact global_source_expression_replay expression source bounded scopes state provenance
    · exact global_source_expression_replay expression source bounded (SourceScopesWithin.append.mp scopes).2 _ provenance
termination_by sizeOf place

theorem global_source_view_replay {typingEnv : TEnv} {env : PEnv} (view : View)
    (source : SourceGlobalEnvironment typingEnv env func)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.viewScopes none view)) :
    ∀ initial upper, GlobalViewReplayAt typingEnv env results vt func returnTypes slots target scopeCount view initial upper := by
  intro initial upper info start finish before after roots typed replay ceiling ready generated native
  apply ReplayBuilder.typedGlobalView typed replay ceiling source.parameters ready generated native
  · intro place same
    cases same
    exact global_source_place_replay place source bounded scopes initial upper
  · intro expression same
    cases same
    exact global_source_expression_replay expression source bounded scopes initial upper
termination_by sizeOf view

theorem global_source_bound_replay {typingEnv : TEnv} {env : PEnv} (bound : Bound)
    (source : SourceGlobalEnvironment typingEnv env func)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.boundScopes none bound)) :
    ∀ initial upper, GlobalBoundReplayAt typingEnv env results vt func returnTypes slots target scopeCount bound initial upper := by
  intro initial upper
  apply globalBoundReplay_of_expression
  intro expression occurrence
  rcases occurrence with rfl | rfl
  all_goals exact global_source_expression_replay expression source bounded scopes initial upper
termination_by sizeOf bound

theorem global_source_expressions_replay {typingEnv : TEnv} {env : PEnv} (expressions : List Expr)
    (source : SourceGlobalEnvironment typingEnv env func)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.exprsScopes none expressions)) :
    ∀ expression ∈ expressions, ∀ initial upper,
      GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount expression initial upper := by
  cases expressions with
  | nil => simp
  | cons first rest =>
    intro expression member
    rcases List.mem_cons.mp member with rfl | member
    · exact global_source_expression_replay expression source bounded (SourceScopesWithin.append.mp scopes).1
    · exact global_source_expressions_replay rest source bounded (SourceScopesWithin.append.mp scopes).2 expression member
termination_by sizeOf expressions
decreasing_by
  all_goals try decreasing_trivial
  all_goals try subst expressions
  all_goals try subst expression
  all_goals simp +arith

theorem global_source_arguments_replay {typingEnv : TEnv} {env : PEnv} (arguments : List Arg)
    (source : SourceGlobalEnvironment typingEnv env func)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.argsScopes none arguments)) :
    ∀ argument ∈ arguments, ∀ initial upper,
      match argument with
      | .byVal expression => GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount expression initial upper
      | .byRef _ place => GlobalPlaceReplayAt typingEnv env results vt func returnTypes slots target scopeCount place initial upper := by
  cases arguments with
  | nil => simp
  | cons first rest =>
    intro argument member
    rcases List.mem_cons.mp member with same | restMember
    · subst argument
      cases first with
      | byVal expression => exact global_source_expression_replay expression source bounded (SourceScopesWithin.append.mp scopes).1
      | byRef mutability place => exact global_source_place_replay place source bounded (SourceScopesWithin.append.mp scopes).1
    · cases first with
      | byVal expression => exact global_source_arguments_replay rest source bounded (SourceScopesWithin.append.mp scopes).2 argument restMember
      | byRef mutability place => exact global_source_arguments_replay rest source bounded (SourceScopesWithin.append.mp scopes).2 argument restMember
termination_by sizeOf arguments

theorem global_source_block_replay {typingEnv : TEnv} {env : PEnv} (body : Core.Block)
    (source : SourceGlobalEnvironment typingEnv env func)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.blockScopes none body)) :
    ∀ loop bindings want initial upper,
      GlobalBlockReplayAt typingEnv env results vt func returnTypes slots target scopeCount loop bindings want body initial upper := by
  intro loop bindings want initial upper
  cases body with
  | mk scope statements value =>
    apply globalBlockReplay_of_children
    · intro nextEnv moduleEq variablesEq implEq modeEq state provenance
      exact global_source_statements_replay statements
        ((source.typingTables moduleEq variablesEq modeEq).scopes (scope :: env.scopes)) bounded
        ((SourceScopesWithin.statements_parent statements (some scope) none).mp
          (SourceScopesWithin.block_parts scopes).2.1) loop scope state provenance
    · intro expression present expressionScopes nextEnv moduleEq variablesEq implEq modeEq state provenance
      exact global_source_expression_replay expression
        ((source.typingTables moduleEq variablesEq modeEq).scopes (scope :: env.scopes)) bounded expressionScopes state provenance
termination_by sizeOf body

theorem global_source_statements_replay {typingEnv : TEnv} {env : PEnv} (statements : List Stmt)
    (source : SourceGlobalEnvironment typingEnv env func)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.stmtsScopes none statements)) :
    ∀ loop scope initial upper,
      GlobalStatementsReplayAt typingEnv env results vt func returnTypes slots target scopeCount loop scope statements initial upper := by
  intro loop scope initial upper
  apply globalStatementsReplay_of_statement source.inside
  intro statement member nextEnv moduleEq variablesEq implEq modeEq state provenance
  exact global_source_statement_replay statement (source.typingTables moduleEq variablesEq modeEq) bounded
    (SourceScopesWithin.stmts_member scopes member) loop scope state provenance
termination_by sizeOf statements

theorem global_source_printargs_replay {typingEnv : TEnv} {env : PEnv} (arguments : List PrintArg)
    (source : SourceGlobalEnvironment typingEnv env func)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.printScopes none arguments)) :
    ∀ expression, PrintArg.expr expression ∈ arguments → ∀ initial upper,
      GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount expression initial upper := by
  cases arguments with
  | nil => simp
  | cons first rest =>
    intro expression member
    cases first with
    | text text =>
      exact global_source_printargs_replay rest source bounded scopes expression (by simpa using member)
    | expr first =>
      rcases List.mem_cons.mp member with same | member
      · cases PrintArg.expr.inj same
        exact global_source_expression_replay expression source bounded (SourceScopesWithin.append.mp scopes).1
      · exact global_source_printargs_replay rest source bounded (SourceScopesWithin.append.mp scopes).2 expression member
termination_by sizeOf arguments

theorem global_source_statement_replay {typingEnv : TEnv} {env : PEnv} (statement : Stmt)
    (source : SourceGlobalEnvironment typingEnv env func)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (scopes : SourceScopesWithin scopeCount (Core.stmtScopes none statement)) :
    ∀ loop scope initial upper,
      GlobalStatementReplayAt typingEnv env results vt func returnTypes slots target scopeCount loop scope statement initial upper := by
  intro loop scope initial upper
  cases statement with
  | letS variableId expression origin => exact globalStatementReplay_let source.variables
  | rebind variableId expression origin => exact globalStatementReplay_rebind source.variables
  | expr expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact globalStatementReplay_expression (global_source_expression_replay expression source bounded scopedBounds initial upper)
  | assign owner expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact globalStatementReplay_assign origin loop scope source.tables source.variables source.parameters
      (global_source_place_replay owner source bounded parts.1 initial upper)
      (fun provenance => global_source_expression_replay expression source bounded parts.2 _ provenance)
  | assignOp op owner expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact globalStatementReplay_assignOp op origin loop scope source.tables source.parameters
      (global_source_place_replay owner source bounded parts.1 initial upper)
      (fun provenance => global_source_expression_replay expression source bounded parts.2 _ provenance)
  | assignWhole owner expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact globalStatementReplay_assignWhole origin loop scope source.tables source.parameters
      (global_source_place_replay owner source bounded parts.1 initial upper)
      (fun provenance => global_source_expression_replay expression source bounded parts.2 _ provenance)
  | append owner view origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact globalStatementReplay_append origin loop scope source.tables source.parameters
      (global_source_place_replay owner source bounded parts.1 initial upper)
      (fun provenance => global_source_view_replay view source bounded parts.2 _ provenance)
  | popN owner count origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    exact globalStatementReplay_popN origin loop scope source.tables source.parameters
      (global_source_place_replay owner source bounded parts.1 initial upper)
      (fun provenance => global_source_expression_replay count source bounded parts.2 _ provenance)
  | resize owner count fill origin =>
    cases fill with
    | none =>
      have scopedBounds := scopes
      simp only [Core.stmtScopes] at scopedBounds
      have parts := SourceScopesWithin.append.mp (SourceScopesWithin.append.mp scopedBounds).1
      exact globalStatementReplay_resizeWithoutFill origin loop scope source.tables source.parameters
        (global_source_place_replay owner source bounded parts.1 initial upper)
        (fun provenance => global_source_expression_replay count source bounded parts.2 _ provenance)
    | some fill =>
      have scopedBounds := scopes
      simp only [Core.stmtScopes] at scopedBounds
      have parts := SourceScopesWithin.append.mp scopedBounds
      have first := SourceScopesWithin.append.mp parts.1
      exact globalStatementReplay_resizeWithFill origin loop scope source.tables source.parameters
        (global_source_place_replay owner source bounded first.1 initial upper)
        (fun provenance => global_source_expression_replay count source bounded first.2 _ provenance)
        (fun provenance => global_source_expression_replay fill source bounded parts.2 _ provenance)
  | clear owner origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact globalStatementReplay_clear origin loop scope source.tables source.parameters
      (global_source_place_replay owner source bounded scopedBounds initial upper)
  | ifS condition yes no origin =>
    cases no with
    | none =>
      have scopedBounds := scopes
      simp only [Core.stmtScopes, List.append_nil] at scopedBounds
      have parts := SourceScopesWithin.append.mp scopedBounds
      apply globalStatementReplay_if source.inside (global_source_expression_replay condition source bounded parts.1 initial upper)
      intro body member state provenance
      rcases member with same | impossible
      · subst body
        exact global_source_block_replay yes source bounded parts.2 loop [] false state provenance
      · cases impossible
    | some no =>
      have scopedBounds := scopes
      simp only [Core.stmtScopes] at scopedBounds
      have parts := SourceScopesWithin.append.mp scopedBounds
      have first := SourceScopesWithin.append.mp parts.1
      apply globalStatementReplay_if source.inside (global_source_expression_replay condition source bounded first.1 initial upper)
      intro body member state provenance
      rcases member with same | same
      · subst body
        exact global_source_block_replay yes source bounded first.2 loop [] false state provenance
      · have identity : body = no := (Option.some.inj same).symm
        subst body
        exact global_source_block_replay no source bounded parts.2 loop [] false state provenance
  | «while» condition body origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    have parts := SourceScopesWithin.append.mp scopedBounds
    apply globalStatementReplay_while source.inside
    · exact global_source_expression_replay condition source bounded parts.1 _ upper
    · intro provenance
      exact global_source_block_replay body (source.typingTables (nextEnv := {typingEnv with loops := typingEnv.loops + 1}) rfl rfl rfl) bounded parts.2 _ _ _ _ provenance
  | forRange variableId low high body origin => exact globalStatementReplay_forRange source.variables
  | forEach variableId index view byRef body origin => exact globalStatementReplay_forEach source.variables
  | ret value origin => exact globalStatementReplay_return source.inside
  | brk origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact globalStatementReplay_break
  | cont origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact globalStatementReplay_continue
  | print arguments origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact globalStatementReplay_print source.tables (global_source_printargs_replay arguments source bounded scopedBounds)
  | assertS expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact globalStatementReplay_assert origin source.tables (global_source_expression_replay expression source bounded scopedBounds initial upper)
  | abort message origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact globalStatementReplay_abort message origin source.tables
  | exit expression origin =>
    have scopedBounds := scopes
    simp only [Core.stmtScopes] at scopedBounds
    exact globalStatementReplay_exit origin source.tables (global_source_expression_replay expression source bounded scopedBounds initial upper)
termination_by sizeOf statement

end

#print axioms global_source_expression_replay
#print axioms global_source_place_replay
#print axioms global_source_view_replay
#print axioms global_source_bound_replay
#print axioms global_source_block_replay
#print axioms global_source_statements_replay
#print axioms global_source_statement_replay
#print axioms global_source_expressions_replay
#print axioms global_source_arguments_replay
#print axioms global_source_printargs_replay

end Goose.Lower.Validation.SummaryPreservation
