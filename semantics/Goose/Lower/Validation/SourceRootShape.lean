import Goose.Lower.Validation.SourceRootShapeReads

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound

private theorem pure_roots_empty {roots : List RootRef}
    (replayed : (pure [] : Core.V (List RootRef)) = .ok roots) : roots = [] := by
  cases replayed
  rfl

private theorem call_result_nonref_empty {callee : Impl} {context : Context} {type : Ty}
    {start finish : Nat} (source : Core.callResultTy callee start = .ok (type, finish))
    (nonref : type.isRefLike = false) {arguments : List (List RootRef)} {roots : List RootRef}
    (replayed : Core.callResultRoots callee context arguments = .ok roots) : roots = [] := by
  cases results : callee.results.toList with
  | nil => apply pure_roots_empty; simpa [Core.callResultRoots, results] using replayed
  | cons result rest =>
    cases rest with
    | nil =>
      simp only [Core.callResultTy, results] at source
      have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      dsimp only at shape
      rw [shape] at nonref
      cases declared : context.resultRoots with
      | nil => apply pure_roots_empty; simpa [Core.callResultRoots, results, declared] using replayed
      | cons row rest =>
        cases rest <;> apply pure_roots_empty <;> simpa [Core.callResultRoots, results, declared, nonref] using replayed
    | cons _ _ => apply pure_roots_empty; simpa [Core.callResultRoots, results] using replayed

mutual

theorem source_expression_nonref_roots_empty (expression : Expr)
    {env : TEnv} {penv : PEnv} (tables : SourceRootTables env penv)
    {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env expression start = .ok (type, finish))
    (nonref : type.isRefLike = false) {before after : RState} {roots : List RootRef}
    (replayed : Core.rpExpr penv expression before = .ok (roots, after)) : roots = [] := by
  cases expression with
  | lit _ _ | bool _ | len _ | un _ _ _ | bin _ _ _ _ | cmp _ _ _ | and _ _ | or _ _
      | not _ | conv _ _ _ _ | pop _ _ | arrLit _ _ | structLit _ _ | fill _ _ =>
    simp only [Core.rpExpr] at replayed
    repeat' first
    | (have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
       exact shape)
    | (obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed)
    | (split at replayed)
  | ref mutability place =>
    obtain ⟨_, _, _, shape, _⟩ := tyExpr_ref_place source
    rw [shape] at nonref
    cases nonref
  | slice mutability view low high origin =>
    obtain ⟨_, _, _, _, _, _, _, _, _, shape⟩ := tyExpr_slice_children source
    rw [shape] at nonref
    cases nonref
  | push owner child origin =>
    obtain ⟨_, _, _, _, _, _, _, _, _, shape⟩ := tyExpr_push_children source
    rw [shape] at nonref
    cases nonref
  | read place =>
    obtain ⟨info, next, placeSource, typeShape⟩ := tyExpr_read_place source
    rw [typeShape] at nonref
    simp only [Core.rpExpr] at replayed
    obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    exact source_readRoots_nonref_empty tables placeSource nonref replayed
  | call context arguments origin =>
    obtain ⟨ctx, callee, _, _, _, contextRow, calleeRow, _, _, resultSource⟩ := tyExpr_call_tables source
    simp only [Core.rpExpr] at replayed
    obtain ⟨argRoots, callStart, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    obtain ⟨_, callReady, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    obtain ⟨actualCtx, actualCallee, actualContext, actualImplementation, _, _, resultReplay⟩ :=
      rpCall_ok penv context argRoots callReady roots after replayed
    rw [tables.moduleEq, contextRow] at actualContext
    cases Option.some.inj actualContext
    rw [tables.moduleEq, calleeRow] at actualImplementation
    cases Option.some.inj actualImplementation
    exact call_result_nonref_empty resultSource nonref resultReplay
  | blockE body =>
    simp only [Core.rpExpr] at replayed
    obtain ⟨result, _, blockReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
    dsimp only at shape
    rw [shape]
    exact source_block_nonref_roots_empty body tables.exprEnv source nonref blockReplay
  | ifE condition thenBody elseBody =>
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨thenType, _, thenSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨elseType, elseFinish, elseSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    by_cases equal : (thenType == elseType) = true
    · simp only [equal, ite_true] at source
      have typeShape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      dsimp only at typeShape
      have typeEq := eq_of_beq equal
      rw [typeShape] at nonref
      simp only [Core.rpExpr] at replayed
      obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
      obtain ⟨thenResult, _, thenReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
      obtain ⟨elseResult, _, elseReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
      have thenEmpty := source_block_nonref_roots_empty thenBody tables.exprEnv thenSource nonref thenReplay
      have elseEmpty := source_block_nonref_roots_empty elseBody tables.exprEnv elseSource
        (by rw [← typeEq]; exact nonref) elseReplay
      have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
      dsimp only at shape
      simpa [thenEmpty, elseEmpty, Core.unionRoots] using shape
    · simp only [equal] at source
      change ((rej .type "the branches of `if` have different types" : Core.T Unit) >>=
        fun _ => pure thenType) elseFinish = .ok (type, finish) at source
      obtain ⟨_, _, rejected, _⟩ := (st_bind_ok _ _ _ _).mp source
      exact (rej_ok _ _ _ _).mp rejected |>.elim

theorem source_block_nonref_roots_empty (body : Core.Block)
    {env : TEnv} {penv : PEnv} (tables : SourceRootTables env penv)
    {sourcePre : List (VarId × Ty)} {rootsPre : List VarId} {type : Ty} {start finish : Nat}
    (source : Core.tyBlock env sourcePre body start = .ok (type, finish))
    (nonref : type.isRefLike = false) {before after : RState} {roots : List RootRef} {range : Nat × Nat}
    (replayed : Core.rpBlockValue penv rootsPre body before = .ok ((roots, range), after)) : roots = [] := by
  cases body with
  | mk scope statements expression =>
    have replayShape := rpBlockValue_ok penv rootsPre scope statements expression before roots range after replayed
    obtain ⟨rootState, _, valueReplay, _⟩ := replayShape.2
    unfold Core.tyBlock at source
    by_cases nested : scope ∈ env.scopes
    · simp [nested, chk] at source
    · simp only [List.contains_iff_mem, nested, ite_false] at source
      obtain ⟨declared, _, declaration, source⟩ := (st_bind_ok _ _ _ _).mp source
      obtain ⟨finalEnv, _, statementsTyped, source⟩ := (st_bind_ok _ _ _ _).mp source
      have declarationTables := declarePre_tables sourcePre declaration
      have finalTables := tyStmts_tables statements statementsTyped
      have resultTables : SourceRootTables finalEnv { penv with scopes := scope :: penv.scopes } := by
        constructor
        · exact tables.moduleEq.trans (finalTables.1.trans declarationTables.1).symm
        · exact tables.variablesEq.trans (finalTables.2.1.trans declarationTables.2.1).symm
      cases expression with
      | none => exact valueReplay.1
      | some expression => exact source_expression_nonref_roots_empty expression resultTables source nonref valueReplay

end

#print axioms source_expression_nonref_roots_empty
#print axioms source_block_nonref_roots_empty

end Goose.Lower.Validation
