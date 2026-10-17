import Goose.Lower.Validation.SourceCanonicalRootFloorsWrites
import Goose.Lower.Validation.SourceCanonicalRootFloorsScopeOrder

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core

def sourceBlockInnerScopeKeys : Block → List Nat
  | .mk _ statements value => (stmtsScopes none statements).map Prod.fst ++
      match value with
      | some expression => (exprScopes none expression).map Prod.fst
      | none => []

theorem sourceBlock_scope_keys (block : Block) (parent : Option Nat) :
    (blockScopes parent block).map Prod.fst =
      sourceBlockScope block :: sourceBlockInnerScopeKeys block := by
  cases block with
  | mk scope statements value =>
    cases value <;> simp only [blockScopes, sourceBlockScope, sourceBlockInnerScopeKeys,
      List.map_cons, List.map_append, List.map_nil, stmtsScopes_keys_none, exprScopes_keys_none]

local macro "source_write_keys_finish " equation:Lean.Parser.Tactic.rwRule ";" "[" _traces:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    rw [$equation]
    simp only [sourceBlockInnerScopeKeys, exprScopes, placeScopes, viewScopes, boundScopes,
      argsScopes, exprsScopes, stmtsScopes, printScopes, stmtScopes, sourceBlock_scope_keys,
      List.map_append, List.map_cons, List.map_nil, List.count_append, List.count_cons,
      List.count_nil, List.append_nil, Prod.fst] at *
    omega))

mutual

theorem sourceExprRootWrites_count (env : PEnv) (expression : Expr) (index : Nat) :
    ((sourceExprRootWrites env expression).map Prod.fst).count index ≤
      ((exprScopes none expression).map Prod.fst).count index := by
  cases expression
  case lit t n =>
    source_write_keys_finish sourceExprRootWrites.eq_def; []
  case bool b =>
    source_write_keys_finish sourceExprRootWrites.eq_def; []
  case read p =>
    have trace0 := sourcePlaceRootWrites_count env p index
    source_write_keys_finish sourceExprRootWrites.eq_def; [trace0]
  case ref m p =>
    have trace0 := sourcePlaceRootWrites_count env p index
    source_write_keys_finish sourceExprRootWrites.eq_def; [trace0]
  case slice m v lo hi org =>
    have trace0 := sourceViewRootWrites_count env v index
    have trace1 := sourceBoundRootWrites_count env lo index
    have trace2 := sourceBoundRootWrites_count env hi index
    source_write_keys_finish sourceExprRootWrites.eq_def; [trace0, trace1, trace2]
  case len v =>
    have trace0 := sourceViewRootWrites_count env v index
    source_write_keys_finish sourceExprRootWrites.eq_def; [trace0]
  case un op e org =>
    have trace0 := sourceExprRootWrites_count env e index
    source_write_keys_finish sourceExprRootWrites.eq_def; [trace0]
  case not e =>
    have trace0 := sourceExprRootWrites_count env e index
    source_write_keys_finish sourceExprRootWrites.eq_def; [trace0]
  case conv k ty e org =>
    have trace0 := sourceExprRootWrites_count env e index
    source_write_keys_finish sourceExprRootWrites.eq_def; [trace0]
  case bin op a b org =>
    have trace0 := sourceExprRootWrites_count env a index
    have trace1 := sourceExprRootWrites_count env b index
    source_write_keys_finish sourceExprRootWrites.eq_def; [trace0, trace1]
  case cmp op a b =>
    have trace0 := sourceExprRootWrites_count env a index
    have trace1 := sourceExprRootWrites_count env b index
    source_write_keys_finish sourceExprRootWrites.eq_def; [trace0, trace1]
  case and a b =>
    have trace0 := sourceExprRootWrites_count env a index
    have trace1 := sourceExprRootWrites_count env b index
    source_write_keys_finish sourceExprRootWrites.eq_def; [trace0, trace1]
  case or a b =>
    have trace0 := sourceExprRootWrites_count env a index
    have trace1 := sourceExprRootWrites_count env b index
    source_write_keys_finish sourceExprRootWrites.eq_def; [trace0, trace1]
  case call c args org =>
    have trace0 := sourceArgumentRootWrites_count env args index
    source_write_keys_finish sourceExprRootWrites.eq_def; [trace0]
  case push p e org =>
    have trace0 := sourcePlaceRootWrites_count env p index
    have trace1 := sourceExprRootWrites_count env e index
    source_write_keys_finish sourceExprRootWrites.eq_def; [trace0, trace1]
  case pop p org =>
    have trace0 := sourcePlaceRootWrites_count env p index
    source_write_keys_finish sourceExprRootWrites.eq_def; [trace0]
  case ifE c yes no =>
    have trace0 := sourceExprRootWrites_count env c index
    have trace1 := sourceBlockRootWrites_count env yes index
    have trace2 := sourceBlockRootWrites_count env no index
    source_write_keys_finish sourceExprRootWrites.eq_def; [trace0, trace1, trace2]
  case blockE b =>
    have trace0 := sourceBlockRootWrites_count env b index
    source_write_keys_finish sourceExprRootWrites.eq_def; [trace0]
  case arrLit ty es =>
    have trace0 := sourceExprListRootWrites_count env es index
    source_write_keys_finish sourceExprRootWrites.eq_def; [trace0]
  case structLit ty es =>
    have trace0 := sourceExprListRootWrites_count env es index
    source_write_keys_finish sourceExprRootWrites.eq_def; [trace0]
  case fill ty e =>
    have trace0 := sourceExprRootWrites_count env e index
    source_write_keys_finish sourceExprRootWrites.eq_def; [trace0]
termination_by sizeOf expression

theorem sourcePlaceRootWrites_count (env : PEnv) (place : Place) (index : Nat) :
    ((sourcePlaceRootWrites env place).map Prod.fst).count index ≤
      ((placeScopes none place).map Prod.fst).count index := by
  cases place
  case var x =>
    source_write_keys_finish sourcePlaceRootWrites.eq_def; []
  case global g =>
    source_write_keys_finish sourcePlaceRootWrites.eq_def; []
  case deref e =>
    have trace0 := sourceExprRootWrites_count env e index
    source_write_keys_finish sourcePlaceRootWrites.eq_def; [trace0]
  case field p i =>
    have trace0 := sourcePlaceRootWrites_count env p index
    source_write_keys_finish sourcePlaceRootWrites.eq_def; [trace0]
  case elem v e org =>
    have trace0 := sourceViewRootWrites_count env v index
    have trace1 := sourceExprRootWrites_count env e index
    source_write_keys_finish sourcePlaceRootWrites.eq_def; [trace0, trace1]
termination_by sizeOf place

theorem sourceViewRootWrites_count (env : PEnv) (view : View) (index : Nat) :
    ((sourceViewRootWrites env view).map Prod.fst).count index ≤
      ((viewScopes none view).map Prod.fst).count index := by
  cases view
  case of p =>
    have trace0 := sourcePlaceRootWrites_count env p index
    source_write_keys_finish sourceViewRootWrites.eq_def; [trace0]
  case val e =>
    have trace0 := sourceExprRootWrites_count env e index
    source_write_keys_finish sourceViewRootWrites.eq_def; [trace0]
termination_by sizeOf view

theorem sourceBoundRootWrites_count (env : PEnv) (bound : Bound) (index : Nat) :
    ((sourceBoundRootWrites env bound).map Prod.fst).count index ≤
      ((boundScopes none bound).map Prod.fst).count index := by
  cases bound
  case omitted =>
    source_write_keys_finish sourceBoundRootWrites.eq_def; []
  case expr e =>
    have trace0 := sourceExprRootWrites_count env e index
    source_write_keys_finish sourceBoundRootWrites.eq_def; [trace0]
  case fromEnd e =>
    have trace0 := sourceExprRootWrites_count env e index
    source_write_keys_finish sourceBoundRootWrites.eq_def; [trace0]
termination_by sizeOf bound

theorem sourceArgumentRootWrites_count (env : PEnv) (arguments : List Arg) (index : Nat) :
    ((sourceArgumentRootWrites env arguments).map Prod.fst).count index ≤
      ((argsScopes none arguments).map Prod.fst).count index := by
  cases arguments
  case nil =>
    source_write_keys_finish sourceArgumentRootWrites.eq_def; []
  case cons head rest =>
    cases head
    case byVal e =>
      have trace0 := sourceExprRootWrites_count env e index
      have trace1 := sourceArgumentRootWrites_count env rest index
      source_write_keys_finish sourceArgumentRootWrites.eq_def; [trace0, trace1]
    case byRef m p =>
      have trace0 := sourcePlaceRootWrites_count env p index
      have trace1 := sourceArgumentRootWrites_count env rest index
      source_write_keys_finish sourceArgumentRootWrites.eq_def; [trace0, trace1]
termination_by sizeOf arguments

theorem sourceExprListRootWrites_count (env : PEnv) (expressions : List Expr) (index : Nat) :
    ((sourceExprListRootWrites env expressions).map Prod.fst).count index ≤
      ((exprsScopes none expressions).map Prod.fst).count index := by
  cases expressions
  case nil =>
    source_write_keys_finish sourceExprListRootWrites.eq_def; []
  case cons e rest =>
    have trace0 := sourceExprRootWrites_count env e index
    have trace1 := sourceExprListRootWrites_count env rest index
    source_write_keys_finish sourceExprListRootWrites.eq_def; [trace0, trace1]
termination_by sizeOf expressions

theorem sourceBlockRootWrites_count (env : PEnv) (block : Block) (index : Nat) :
    ((sourceBlockRootWrites env block).map Prod.fst).count index ≤
      (sourceBlockInnerScopeKeys block).count index := by
  cases block
  case mk scope stmts value =>
    cases value
    case none =>
      have trace0 := sourceStmtListRootWrites_count ({ env with scopes := scope :: env.scopes }) stmts index
      source_write_keys_finish sourceBlockRootWrites.eq_def; [trace0]
    case some e =>
      have trace0 := sourceStmtListRootWrites_count ({ env with scopes := scope :: env.scopes }) stmts index
      have trace1 := sourceExprRootWrites_count ({ env with scopes := scope :: env.scopes }) e index
      source_write_keys_finish sourceBlockRootWrites.eq_def; [trace0, trace1]
termination_by sizeOf block

theorem sourceStmtListRootWrites_count (env : PEnv) (statements : List Stmt) (index : Nat) :
    ((sourceStmtListRootWrites env statements).map Prod.fst).count index ≤
      ((stmtsScopes none statements).map Prod.fst).count index := by
  cases statements
  case nil =>
    source_write_keys_finish sourceStmtListRootWrites.eq_def; []
  case cons statement rest =>
    have trace0 := sourceStmtRootWrites_count env statement index
    have trace1 := sourceStmtListRootWrites_count env rest index
    source_write_keys_finish sourceStmtListRootWrites.eq_def; [trace0, trace1]
termination_by sizeOf statements

theorem sourcePrintRootWrites_count (env : PEnv) (arguments : List PrintArg) (index : Nat) :
    ((sourcePrintRootWrites env arguments).map Prod.fst).count index ≤
      ((printScopes none arguments).map Prod.fst).count index := by
  cases arguments
  case nil =>
    source_write_keys_finish sourcePrintRootWrites.eq_def; []
  case cons head rest =>
    cases head
    case text txt =>
      have trace0 := sourcePrintRootWrites_count env rest index
      source_write_keys_finish sourcePrintRootWrites.eq_def; [trace0]
    case expr e =>
      have trace0 := sourceExprRootWrites_count env e index
      have trace1 := sourcePrintRootWrites_count env rest index
      source_write_keys_finish sourcePrintRootWrites.eq_def; [trace0, trace1]
termination_by sizeOf arguments

theorem sourceStmtRootWrites_count (env : PEnv) (statement : Stmt) (index : Nat) :
    ((sourceStmtRootWrites env statement).map Prod.fst).count index ≤
      ((stmtScopes none statement).map Prod.fst).count index := by
  cases statement
  case letS x e org =>
    have trace0 := sourceExprRootWrites_count env e index
    source_write_keys_finish sourceStmtRootWrites.eq_def; [trace0]
  case rebind x e org =>
    have trace0 := sourceExprRootWrites_count env e index
    source_write_keys_finish sourceStmtRootWrites.eq_def; [trace0]
  case expr e org =>
    have trace0 := sourceExprRootWrites_count env e index
    source_write_keys_finish sourceStmtRootWrites.eq_def; [trace0]
  case assertS e org =>
    have trace0 := sourceExprRootWrites_count env e index
    source_write_keys_finish sourceStmtRootWrites.eq_def; [trace0]
  case exit e org =>
    have trace0 := sourceExprRootWrites_count env e index
    source_write_keys_finish sourceStmtRootWrites.eq_def; [trace0]
  case assign p e org =>
    have trace0 := sourcePlaceRootWrites_count env p index
    have trace1 := sourceExprRootWrites_count env e index
    source_write_keys_finish sourceStmtRootWrites.eq_def; [trace0, trace1]
  case assignOp op p e org =>
    have trace0 := sourcePlaceRootWrites_count env p index
    have trace1 := sourceExprRootWrites_count env e index
    source_write_keys_finish sourceStmtRootWrites.eq_def; [trace0, trace1]
  case assignWhole p e org =>
    have trace0 := sourcePlaceRootWrites_count env p index
    have trace1 := sourceExprRootWrites_count env e index
    source_write_keys_finish sourceStmtRootWrites.eq_def; [trace0, trace1]
  case popN p e org =>
    have trace0 := sourcePlaceRootWrites_count env p index
    have trace1 := sourceExprRootWrites_count env e index
    source_write_keys_finish sourceStmtRootWrites.eq_def; [trace0, trace1]
  case append p v org =>
    have trace0 := sourcePlaceRootWrites_count env p index
    have trace1 := sourceViewRootWrites_count env v index
    source_write_keys_finish sourceStmtRootWrites.eq_def; [trace0, trace1]
  case clear p org =>
    have trace0 := sourcePlaceRootWrites_count env p index
    source_write_keys_finish sourceStmtRootWrites.eq_def; [trace0]
  case «while» c b org =>
    have trace0 := sourceExprRootWrites_count env c index
    have trace1 := sourceBlockRootWrites_count env b index
    source_write_keys_finish sourceStmtRootWrites.eq_def; [trace0, trace1]
  case forRange x lo hi b org =>
    have trace0 := sourceExprRootWrites_count env lo index
    have trace1 := sourceExprRootWrites_count env hi index
    have trace2 := sourceBlockRootWrites_count env b index
    source_write_keys_finish sourceStmtRootWrites.eq_def; [trace0, trace1, trace2]
  case forEach x i v byReference b org =>
    have trace0 := sourceViewRootWrites_count env v index
    have trace1 := sourceBlockRootWrites_count env b index
    source_write_keys_finish sourceStmtRootWrites.eq_def; [trace0, trace1]
  case brk org =>
    source_write_keys_finish sourceStmtRootWrites.eq_def; []
  case cont org =>
    source_write_keys_finish sourceStmtRootWrites.eq_def; []
  case abort msg org =>
    source_write_keys_finish sourceStmtRootWrites.eq_def; []
  case print args org =>
    have trace0 := sourcePrintRootWrites_count env args index
    source_write_keys_finish sourceStmtRootWrites.eq_def; [trace0]
  case resize p count fill org =>
    cases fill
    case none =>
      have trace0 := sourcePlaceRootWrites_count env p index
      have trace1 := sourceExprRootWrites_count env count index
      source_write_keys_finish sourceStmtRootWrites.eq_def; [trace0, trace1]
    case some child =>
      have trace0 := sourcePlaceRootWrites_count env p index
      have trace1 := sourceExprRootWrites_count env count index
      have trace2 := sourceExprRootWrites_count env child index
      source_write_keys_finish sourceStmtRootWrites.eq_def; [trace0, trace1, trace2]
  case ifS c yes no org =>
    cases no
    case none =>
      have trace0 := sourceExprRootWrites_count env c index
      have trace1 := sourceBlockRootWrites_count env yes index
      source_write_keys_finish sourceStmtRootWrites.eq_def; [trace0, trace1]
    case some child =>
      have trace0 := sourceExprRootWrites_count env c index
      have trace1 := sourceBlockRootWrites_count env yes index
      have trace2 := sourceBlockRootWrites_count env child index
      source_write_keys_finish sourceStmtRootWrites.eq_def; [trace0, trace1, trace2]
  case ret value org =>
    cases value
    case none =>
      source_write_keys_finish sourceStmtRootWrites.eq_def; []
    case some child =>
      have trace0 := sourceExprRootWrites_count env child index
      source_write_keys_finish sourceStmtRootWrites.eq_def; [trace0]
termination_by sizeOf statement

end

def sourceNodeRootWrites (env : PEnv) : DemandNode → List SourceRootWrite
  | .expression expression => sourceExprRootWrites env expression
  | .place place => sourcePlaceRootWrites env place
  | .view view => sourceViewRootWrites env view
  | .bound bound => sourceBoundRootWrites env bound
  | .statement statement => sourceStmtRootWrites env statement
  | .block block => sourceBlockRootWrites env block

def sourceNodeScopeKeys : DemandNode → List Nat
  | .expression expression => (exprScopes none expression).map Prod.fst
  | .place place => (placeScopes none place).map Prod.fst
  | .view view => (viewScopes none view).map Prod.fst
  | .bound bound => (boundScopes none bound).map Prod.fst
  | .statement statement => (stmtScopes none statement).map Prod.fst
  | .block block => (blockScopes none block).map Prod.fst

theorem sourceNodeRootWrites_count (env : PEnv) (node : DemandNode) (index : Nat) :
    ((sourceNodeRootWrites env node).map Prod.fst).count index ≤
      (sourceNodeScopeKeys node).count index := by
  cases node with
  | expression expression => exact sourceExprRootWrites_count env expression index
  | place place => exact sourcePlaceRootWrites_count env place index
  | view view => exact sourceViewRootWrites_count env view index
  | bound bound => exact sourceBoundRootWrites_count env bound index
  | statement statement => exact sourceStmtRootWrites_count env statement index
  | block block =>
    exact Nat.le_trans (sourceBlockRootWrites_count env block index) (by
      rw [sourceNodeScopeKeys, sourceBlock_scope_keys]
      exact List.count_le_count_cons)

theorem sourceNodeRootWrites_nodup (env : PEnv) (node : DemandNode)
    (unique : (sourceNodeScopeKeys node).Nodup) :
    ((sourceNodeRootWrites env node).map Prod.fst).Nodup := by
  apply List.nodup_iff_count.mpr
  intro index
  exact Nat.le_trans (sourceNodeRootWrites_count env node index) (List.nodup_iff_count.mp unique index)

theorem sourceNodeRootWrites_scope (env : PEnv) (node : DemandNode)
    (entry : SourceRootWrite) (member : entry ∈ sourceNodeRootWrites env node) :
    entry.1 ∈ sourceNodeScopeKeys node := by
  have positive : 0 < ((sourceNodeRootWrites env node).map Prod.fst).count entry.1 :=
    List.count_pos_iff.mpr (List.mem_map.mpr ⟨entry, member, rfl⟩)
  exact List.count_pos_iff.mp (Nat.lt_of_lt_of_le positive (sourceNodeRootWrites_count env node entry.1))

end Goose.Lower.Validation.SourceCanonicalRootFloors
