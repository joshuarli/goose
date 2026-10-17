import Goose.Lower.Validation.SourceCanonicalRootFloorsWriteLookup

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core

local macro "source_write_scopes_finish " equation:Lean.Parser.Tactic.rwRule ";" "[" traces:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    all_goals conv =>
      lhs
      rw [$equation]
    all_goals conv =>
      rhs
      rw [$equation]
    all_goals simp only [collectSourceBlockRoots_scopes, $traces,*]
    all_goals rfl))

mutual

theorem sourceExprRootWrites_scopes (env : PEnv) (scopes : List Nat) (expression : Expr) :
    sourceExprRootWrites { env with scopes := scopes } expression = sourceExprRootWrites env expression := by
  cases expression
  case lit t n =>
    source_write_scopes_finish sourceExprRootWrites.eq_def; []
  case bool b =>
    source_write_scopes_finish sourceExprRootWrites.eq_def; []
  case read p =>
    have trace0 := sourcePlaceRootWrites_scopes env scopes p
    source_write_scopes_finish sourceExprRootWrites.eq_def; [trace0]
  case ref m p =>
    have trace0 := sourcePlaceRootWrites_scopes env scopes p
    source_write_scopes_finish sourceExprRootWrites.eq_def; [trace0]
  case slice m v lo hi org =>
    have trace0 := sourceViewRootWrites_scopes env scopes v
    have trace1 := sourceBoundRootWrites_scopes env scopes lo
    have trace2 := sourceBoundRootWrites_scopes env scopes hi
    source_write_scopes_finish sourceExprRootWrites.eq_def; [trace0, trace1, trace2]
  case len v =>
    have trace0 := sourceViewRootWrites_scopes env scopes v
    source_write_scopes_finish sourceExprRootWrites.eq_def; [trace0]
  case un op e org =>
    have trace0 := sourceExprRootWrites_scopes env scopes e
    source_write_scopes_finish sourceExprRootWrites.eq_def; [trace0]
  case not e =>
    have trace0 := sourceExprRootWrites_scopes env scopes e
    source_write_scopes_finish sourceExprRootWrites.eq_def; [trace0]
  case conv k ty e org =>
    have trace0 := sourceExprRootWrites_scopes env scopes e
    source_write_scopes_finish sourceExprRootWrites.eq_def; [trace0]
  case bin op a b org =>
    have trace0 := sourceExprRootWrites_scopes env scopes a
    have trace1 := sourceExprRootWrites_scopes env scopes b
    source_write_scopes_finish sourceExprRootWrites.eq_def; [trace0, trace1]
  case cmp op a b =>
    have trace0 := sourceExprRootWrites_scopes env scopes a
    have trace1 := sourceExprRootWrites_scopes env scopes b
    source_write_scopes_finish sourceExprRootWrites.eq_def; [trace0, trace1]
  case and a b =>
    have trace0 := sourceExprRootWrites_scopes env scopes a
    have trace1 := sourceExprRootWrites_scopes env scopes b
    source_write_scopes_finish sourceExprRootWrites.eq_def; [trace0, trace1]
  case or a b =>
    have trace0 := sourceExprRootWrites_scopes env scopes a
    have trace1 := sourceExprRootWrites_scopes env scopes b
    source_write_scopes_finish sourceExprRootWrites.eq_def; [trace0, trace1]
  case call c args org =>
    have trace0 := sourceArgumentRootWrites_scopes env scopes args
    source_write_scopes_finish sourceExprRootWrites.eq_def; [trace0]
  case push p e org =>
    have trace0 := sourcePlaceRootWrites_scopes env scopes p
    have trace1 := sourceExprRootWrites_scopes env scopes e
    source_write_scopes_finish sourceExprRootWrites.eq_def; [trace0, trace1]
  case pop p org =>
    have trace0 := sourcePlaceRootWrites_scopes env scopes p
    source_write_scopes_finish sourceExprRootWrites.eq_def; [trace0]
  case ifE c yes no =>
    have trace0 := sourceExprRootWrites_scopes env scopes c
    have trace1 := sourceBlockRootWrites_scopes env scopes yes
    have trace2 := sourceBlockRootWrites_scopes env scopes no
    source_write_scopes_finish sourceExprRootWrites.eq_def; [trace0, trace1, trace2]
  case blockE b =>
    have trace0 := sourceBlockRootWrites_scopes env scopes b
    source_write_scopes_finish sourceExprRootWrites.eq_def; [trace0]
  case arrLit ty es =>
    have trace0 := sourceExprListRootWrites_scopes env scopes es
    source_write_scopes_finish sourceExprRootWrites.eq_def; [trace0]
  case structLit ty es =>
    have trace0 := sourceExprListRootWrites_scopes env scopes es
    source_write_scopes_finish sourceExprRootWrites.eq_def; [trace0]
  case fill ty e =>
    have trace0 := sourceExprRootWrites_scopes env scopes e
    source_write_scopes_finish sourceExprRootWrites.eq_def; [trace0]
termination_by sizeOf expression

theorem sourcePlaceRootWrites_scopes (env : PEnv) (scopes : List Nat) (place : Place) :
    sourcePlaceRootWrites { env with scopes := scopes } place = sourcePlaceRootWrites env place := by
  cases place
  case var x =>
    source_write_scopes_finish sourcePlaceRootWrites.eq_def; []
  case global g =>
    source_write_scopes_finish sourcePlaceRootWrites.eq_def; []
  case deref e =>
    have trace0 := sourceExprRootWrites_scopes env scopes e
    source_write_scopes_finish sourcePlaceRootWrites.eq_def; [trace0]
  case field p i =>
    have trace0 := sourcePlaceRootWrites_scopes env scopes p
    source_write_scopes_finish sourcePlaceRootWrites.eq_def; [trace0]
  case elem v e org =>
    have trace0 := sourceViewRootWrites_scopes env scopes v
    have trace1 := sourceExprRootWrites_scopes env scopes e
    source_write_scopes_finish sourcePlaceRootWrites.eq_def; [trace0, trace1]
termination_by sizeOf place

theorem sourceViewRootWrites_scopes (env : PEnv) (scopes : List Nat) (view : View) :
    sourceViewRootWrites { env with scopes := scopes } view = sourceViewRootWrites env view := by
  cases view
  case of p =>
    have trace0 := sourcePlaceRootWrites_scopes env scopes p
    source_write_scopes_finish sourceViewRootWrites.eq_def; [trace0]
  case val e =>
    have trace0 := sourceExprRootWrites_scopes env scopes e
    source_write_scopes_finish sourceViewRootWrites.eq_def; [trace0]
termination_by sizeOf view

theorem sourceBoundRootWrites_scopes (env : PEnv) (scopes : List Nat) (bound : Bound) :
    sourceBoundRootWrites { env with scopes := scopes } bound = sourceBoundRootWrites env bound := by
  cases bound
  case omitted =>
    source_write_scopes_finish sourceBoundRootWrites.eq_def; []
  case expr e =>
    have trace0 := sourceExprRootWrites_scopes env scopes e
    source_write_scopes_finish sourceBoundRootWrites.eq_def; [trace0]
  case fromEnd e =>
    have trace0 := sourceExprRootWrites_scopes env scopes e
    source_write_scopes_finish sourceBoundRootWrites.eq_def; [trace0]
termination_by sizeOf bound

theorem sourceArgumentRootWrites_scopes (env : PEnv) (scopes : List Nat) (arguments : List Arg) :
    sourceArgumentRootWrites { env with scopes := scopes } arguments = sourceArgumentRootWrites env arguments := by
  cases arguments
  case nil =>
    source_write_scopes_finish sourceArgumentRootWrites.eq_def; []
  case cons head rest =>
    cases head
    case byVal e =>
      have trace0 := sourceExprRootWrites_scopes env scopes e
      have trace1 := sourceArgumentRootWrites_scopes env scopes rest
      source_write_scopes_finish sourceArgumentRootWrites.eq_def; [trace0, trace1]
    case byRef m p =>
      have trace0 := sourcePlaceRootWrites_scopes env scopes p
      have trace1 := sourceArgumentRootWrites_scopes env scopes rest
      source_write_scopes_finish sourceArgumentRootWrites.eq_def; [trace0, trace1]
termination_by sizeOf arguments

theorem sourceExprListRootWrites_scopes (env : PEnv) (scopes : List Nat) (expressions : List Expr) :
    sourceExprListRootWrites { env with scopes := scopes } expressions = sourceExprListRootWrites env expressions := by
  cases expressions
  case nil =>
    source_write_scopes_finish sourceExprListRootWrites.eq_def; []
  case cons e rest =>
    have trace0 := sourceExprRootWrites_scopes env scopes e
    have trace1 := sourceExprListRootWrites_scopes env scopes rest
    source_write_scopes_finish sourceExprListRootWrites.eq_def; [trace0, trace1]
termination_by sizeOf expressions

theorem sourceBlockRootWrites_scopes (env : PEnv) (scopes : List Nat) (block : Block) :
    sourceBlockRootWrites { env with scopes := scopes } block = sourceBlockRootWrites env block := by
  cases block
  case mk scope stmts value =>
    cases value
    case none =>
      have trace0 := (sourceStmtListRootWrites_scopes env (scope :: scopes) stmts).trans (sourceStmtListRootWrites_scopes env (scope :: env.scopes) stmts).symm
      source_write_scopes_finish sourceBlockRootWrites.eq_def; [trace0]
    case some e =>
      have trace0 := (sourceStmtListRootWrites_scopes env (scope :: scopes) stmts).trans (sourceStmtListRootWrites_scopes env (scope :: env.scopes) stmts).symm
      have trace1 := (sourceExprRootWrites_scopes env (scope :: scopes) e).trans (sourceExprRootWrites_scopes env (scope :: env.scopes) e).symm
      source_write_scopes_finish sourceBlockRootWrites.eq_def; [trace0, trace1]
termination_by sizeOf block

theorem sourceStmtListRootWrites_scopes (env : PEnv) (scopes : List Nat) (statements : List Stmt) :
    sourceStmtListRootWrites { env with scopes := scopes } statements = sourceStmtListRootWrites env statements := by
  cases statements
  case nil =>
    source_write_scopes_finish sourceStmtListRootWrites.eq_def; []
  case cons statement rest =>
    have trace0 := sourceStmtRootWrites_scopes env scopes statement
    have trace1 := sourceStmtListRootWrites_scopes env scopes rest
    source_write_scopes_finish sourceStmtListRootWrites.eq_def; [trace0, trace1]
termination_by sizeOf statements

theorem sourcePrintRootWrites_scopes (env : PEnv) (scopes : List Nat) (arguments : List PrintArg) :
    sourcePrintRootWrites { env with scopes := scopes } arguments = sourcePrintRootWrites env arguments := by
  cases arguments
  case nil =>
    source_write_scopes_finish sourcePrintRootWrites.eq_def; []
  case cons head rest =>
    cases head
    case text txt =>
      have trace0 := sourcePrintRootWrites_scopes env scopes rest
      source_write_scopes_finish sourcePrintRootWrites.eq_def; [trace0]
    case expr e =>
      have trace0 := sourceExprRootWrites_scopes env scopes e
      have trace1 := sourcePrintRootWrites_scopes env scopes rest
      source_write_scopes_finish sourcePrintRootWrites.eq_def; [trace0, trace1]
termination_by sizeOf arguments

theorem sourceStmtRootWrites_scopes (env : PEnv) (scopes : List Nat) (statement : Stmt) :
    sourceStmtRootWrites { env with scopes := scopes } statement = sourceStmtRootWrites env statement := by
  cases statement
  case letS x e org =>
    have trace0 := sourceExprRootWrites_scopes env scopes e
    source_write_scopes_finish sourceStmtRootWrites.eq_def; [trace0]
  case rebind x e org =>
    have trace0 := sourceExprRootWrites_scopes env scopes e
    source_write_scopes_finish sourceStmtRootWrites.eq_def; [trace0]
  case expr e org =>
    have trace0 := sourceExprRootWrites_scopes env scopes e
    source_write_scopes_finish sourceStmtRootWrites.eq_def; [trace0]
  case assertS e org =>
    have trace0 := sourceExprRootWrites_scopes env scopes e
    source_write_scopes_finish sourceStmtRootWrites.eq_def; [trace0]
  case exit e org =>
    have trace0 := sourceExprRootWrites_scopes env scopes e
    source_write_scopes_finish sourceStmtRootWrites.eq_def; [trace0]
  case assign p e org =>
    have trace0 := sourcePlaceRootWrites_scopes env scopes p
    have trace1 := sourceExprRootWrites_scopes env scopes e
    source_write_scopes_finish sourceStmtRootWrites.eq_def; [trace0, trace1]
  case assignOp op p e org =>
    have trace0 := sourcePlaceRootWrites_scopes env scopes p
    have trace1 := sourceExprRootWrites_scopes env scopes e
    source_write_scopes_finish sourceStmtRootWrites.eq_def; [trace0, trace1]
  case assignWhole p e org =>
    have trace0 := sourcePlaceRootWrites_scopes env scopes p
    have trace1 := sourceExprRootWrites_scopes env scopes e
    source_write_scopes_finish sourceStmtRootWrites.eq_def; [trace0, trace1]
  case popN p e org =>
    have trace0 := sourcePlaceRootWrites_scopes env scopes p
    have trace1 := sourceExprRootWrites_scopes env scopes e
    source_write_scopes_finish sourceStmtRootWrites.eq_def; [trace0, trace1]
  case append p v org =>
    have trace0 := sourcePlaceRootWrites_scopes env scopes p
    have trace1 := sourceViewRootWrites_scopes env scopes v
    source_write_scopes_finish sourceStmtRootWrites.eq_def; [trace0, trace1]
  case clear p org =>
    have trace0 := sourcePlaceRootWrites_scopes env scopes p
    source_write_scopes_finish sourceStmtRootWrites.eq_def; [trace0]
  case «while» c b org =>
    have trace0 := sourceExprRootWrites_scopes env scopes c
    have trace1 := sourceBlockRootWrites_scopes env scopes b
    source_write_scopes_finish sourceStmtRootWrites.eq_def; [trace0, trace1]
  case forRange x lo hi b org =>
    have trace0 := sourceExprRootWrites_scopes env scopes lo
    have trace1 := sourceExprRootWrites_scopes env scopes hi
    have trace2 := sourceBlockRootWrites_scopes env scopes b
    source_write_scopes_finish sourceStmtRootWrites.eq_def; [trace0, trace1, trace2]
  case forEach x i v byReference b org =>
    have trace0 := sourceViewRootWrites_scopes env scopes v
    have trace1 := sourceBlockRootWrites_scopes env scopes b
    source_write_scopes_finish sourceStmtRootWrites.eq_def; [trace0, trace1]
  case brk org =>
    source_write_scopes_finish sourceStmtRootWrites.eq_def; []
  case cont org =>
    source_write_scopes_finish sourceStmtRootWrites.eq_def; []
  case abort msg org =>
    source_write_scopes_finish sourceStmtRootWrites.eq_def; []
  case print args org =>
    have trace0 := sourcePrintRootWrites_scopes env scopes args
    source_write_scopes_finish sourceStmtRootWrites.eq_def; [trace0]
  case resize p count fill org =>
    cases fill
    case none =>
      have trace0 := sourcePlaceRootWrites_scopes env scopes p
      have trace1 := sourceExprRootWrites_scopes env scopes count
      source_write_scopes_finish sourceStmtRootWrites.eq_def; [trace0, trace1]
    case some child =>
      have trace0 := sourcePlaceRootWrites_scopes env scopes p
      have trace1 := sourceExprRootWrites_scopes env scopes count
      have trace2 := sourceExprRootWrites_scopes env scopes child
      source_write_scopes_finish sourceStmtRootWrites.eq_def; [trace0, trace1, trace2]
  case ifS c yes no org =>
    cases no
    case none =>
      have trace0 := sourceExprRootWrites_scopes env scopes c
      have trace1 := sourceBlockRootWrites_scopes env scopes yes
      source_write_scopes_finish sourceStmtRootWrites.eq_def; [trace0, trace1]
    case some child =>
      have trace0 := sourceExprRootWrites_scopes env scopes c
      have trace1 := sourceBlockRootWrites_scopes env scopes yes
      have trace2 := sourceBlockRootWrites_scopes env scopes child
      source_write_scopes_finish sourceStmtRootWrites.eq_def; [trace0, trace1, trace2]
  case ret value org =>
    cases value
    case none =>
      source_write_scopes_finish sourceStmtRootWrites.eq_def; []
    case some child =>
      have trace0 := sourceExprRootWrites_scopes env scopes child
      source_write_scopes_finish sourceStmtRootWrites.eq_def; [trace0]
termination_by sizeOf statement

end

theorem sourceNodeRootWrites_scopes (env : PEnv) (scopes : List Nat) (node : DemandNode) :
    sourceNodeRootWrites { env with scopes := scopes } node = sourceNodeRootWrites env node := by
  cases node <;> first
    | exact sourceExprRootWrites_scopes _ _ _
    | exact sourcePlaceRootWrites_scopes _ _ _
    | exact sourceViewRootWrites_scopes _ _ _
    | exact sourceBoundRootWrites_scopes _ _ _
    | exact sourceStmtRootWrites_scopes _ _ _
    | exact sourceBlockRootWrites_scopes _ _ _

end Goose.Lower.Validation.SourceCanonicalRootFloors
