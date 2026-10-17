import Goose.Lower.Validation.SourceCanonicalRootFloorsTableIndependence
import Goose.Lower.Validation.SourceCanonicalRootFloorsEnvironments

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core

abbrev SourceRootWrite := Nat × List RootRef

def applySourceRootWrites (writes : List SourceRootWrite) (table : SourceRootTable) : SourceRootTable :=
  writes.foldl (fun current entry =>
    if entry.1 < current.size then current.set! entry.1 (some entry.2) else current) table

theorem applySourceRootWrites_append (first second : List SourceRootWrite) (table : SourceRootTable) :
    applySourceRootWrites (first ++ second) table =
      applySourceRootWrites second (applySourceRootWrites first table) := by
  exact List.foldl_append

mutual

def sourceExprRootWrites (env : PEnv) : Expr → List SourceRootWrite
  | .lit .. | .bool .. => []
  | .read p | .ref _ p | .pop p _ => sourcePlaceRootWrites env p
  | .slice _ v lo hi _ => sourceViewRootWrites env v ++ sourceBoundRootWrites env lo ++ sourceBoundRootWrites env hi
  | .len v => sourceViewRootWrites env v
  | .un _ e _ | .not e | .conv _ _ e _ | .fill _ e => sourceExprRootWrites env e
  | .bin _ a b _ | .cmp _ a b | .and a b | .or a b => sourceExprRootWrites env a ++ sourceExprRootWrites env b
  | .call _ args _ => sourceArgumentRootWrites env args
  | .push p e _ => sourcePlaceRootWrites env p ++ sourceExprRootWrites env e
  | .ifE c yes no => sourceExprRootWrites env c ++ sourceBlockRootWrites env yes ++
      sourceBlockRootWrites env no ++ [(sourceBlockScope yes,
        unionRoots (collectSourceBlockRoots env yes #[]).1 (collectSourceBlockRoots env no #[]).1)]
  | .blockE b => sourceBlockRootWrites env b
  | .arrLit _ es | .structLit _ es => sourceExprListRootWrites env es

def sourcePlaceRootWrites (env : PEnv) : Place → List SourceRootWrite
  | .var _ | .global _ => []
  | .deref e => sourceExprRootWrites env e
  | .field p _ => sourcePlaceRootWrites env p
  | .elem v e _ => sourceViewRootWrites env v ++ sourceExprRootWrites env e

def sourceViewRootWrites (env : PEnv) : View → List SourceRootWrite
  | .of p => sourcePlaceRootWrites env p
  | .val e => sourceExprRootWrites env e

def sourceBoundRootWrites (env : PEnv) : Bound → List SourceRootWrite
  | .omitted => []
  | .expr e | .fromEnd e => sourceExprRootWrites env e

def sourceArgumentRootWrites (env : PEnv) : List Arg → List SourceRootWrite
  | [] => []
  | .byVal e :: rest => sourceExprRootWrites env e ++ sourceArgumentRootWrites env rest
  | .byRef _ p :: rest => sourcePlaceRootWrites env p ++ sourceArgumentRootWrites env rest

def sourceExprListRootWrites (env : PEnv) : List Expr → List SourceRootWrite
  | [] => []
  | e :: rest => sourceExprRootWrites env e ++ sourceExprListRootWrites env rest

def sourceBlockRootWrites (env : PEnv) : Block → List SourceRootWrite
  | .mk scope stmts value => sourceStmtListRootWrites { env with scopes := scope :: env.scopes } stmts ++
      match value with
      | some e => sourceExprRootWrites { env with scopes := scope :: env.scopes } e
      | none => []

def sourceStmtListRootWrites (env : PEnv) : List Stmt → List SourceRootWrite
  | [] => []
  | s :: rest => sourceStmtRootWrites env s ++ sourceStmtListRootWrites env rest

def sourcePrintRootWrites (env : PEnv) : List PrintArg → List SourceRootWrite
  | [] => []
  | .text _ :: rest => sourcePrintRootWrites env rest
  | .expr e :: rest => sourceExprRootWrites env e ++ sourcePrintRootWrites env rest

def sourceStmtRootWrites (env : PEnv) : Stmt → List SourceRootWrite
  | .letS _ e _ | .rebind _ e _ | .expr e _ | .assertS e _ | .exit e _ => sourceExprRootWrites env e
  | .assign p e _ | .assignOp _ p e _ | .assignWhole p e _ | .popN p e _ =>
      sourcePlaceRootWrites env p ++ sourceExprRootWrites env e
  | .append p v _ => sourcePlaceRootWrites env p ++ sourceViewRootWrites env v
  | .resize p e fill _ => sourcePlaceRootWrites env p ++ sourceExprRootWrites env e ++
      match fill with
      | some value => sourceExprRootWrites env value
      | none => []
  | .clear p _ => sourcePlaceRootWrites env p
  | .ifS c yes no _ => sourceExprRootWrites env c ++ sourceBlockRootWrites env yes ++
      match no with
      | some block => sourceBlockRootWrites env block
      | none => []
  | .while c b _ => sourceExprRootWrites env c ++ sourceBlockRootWrites env b
  | .forRange _ lo hi b _ => sourceExprRootWrites env lo ++ sourceExprRootWrites env hi ++ sourceBlockRootWrites env b
  | .forEach _ _ v _ b _ => sourceViewRootWrites env v ++ sourceBlockRootWrites env b
  | .ret value _ => match value with
      | some e => sourceExprRootWrites env e
      | none => []
  | .brk _ | .cont _ | .abort .. => []
  | .print args _ => sourcePrintRootWrites env args

end

private theorem canonicalExpr (env : PEnv) (expression : Expr) (table : SourceRootTable) :
    (collectSourceExprRoots env expression table).1 = (collectSourceExprRoots env expression #[]).1 :=
  collectSourceExprRoots_independent env expression table #[]

private theorem canonicalPlace (env : PEnv) (place : Place) (table : SourceRootTable) :
    (collectSourcePlaceRoots env place table).1 = (collectSourcePlaceRoots env place #[]).1 :=
  collectSourcePlaceRoots_independent env place table #[]

private theorem canonicalView (env : PEnv) (view : View) (table : SourceRootTable) :
    (collectSourceViewRoots env view table).1 = (collectSourceViewRoots env view #[]).1 :=
  collectSourceViewRoots_independent env view table #[]

private theorem canonicalArgument (env : PEnv) (arguments : List Arg) (table : SourceRootTable) :
    (collectSourceArgumentRoots env arguments table).1 = (collectSourceArgumentRoots env arguments #[]).1 :=
  collectSourceArgumentRoots_independent env arguments table #[]

private theorem canonicalBlock (env : PEnv) (block : Block) (table : SourceRootTable) :
    (collectSourceBlockRoots env block table).1 = (collectSourceBlockRoots env block #[]).1 :=
  collectSourceBlockRoots_independent env block table #[]

private theorem source_bind_apply (action : SourceRootsM α) (next : α → SourceRootsM β)
    (table : SourceRootTable) :
    ((action >>= next) table) = next (action table).1 (action table).2 := by
  change (match action table with | (value, after) => next value after) = _
  cases action table
  rfl

private theorem source_pure_apply (value : α) (table : SourceRootTable) :
    ((pure value : SourceRootsM α) table) = (value, table) := rfl

private theorem source_modify_apply (step : SourceRootTable → SourceRootTable)
    (table : SourceRootTable) :
    ((modify step : SourceRootsM Unit) table) = ((), step table) := rfl

local macro "source_writes_finish " equation:Lean.Parser.Tactic.rwRule "," writes:Lean.Parser.Tactic.rwRule ";" "[" traces:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    conv =>
      lhs
      rw [$equation]
    rw [$writes]
    simp only [source_bind_apply, source_pure_apply, source_modify_apply,
      Prod.fst, Prod.snd, List.append_nil, applySourceRootWrites_append,
      canonicalExpr, canonicalPlace, canonicalView, canonicalArgument, canonicalBlock, $traces,*]
    all_goals rfl))

mutual

theorem collectSourceExprRoots_writes (env : PEnv) (expression : Expr) (table : SourceRootTable) :
    (collectSourceExprRoots env expression table).2 =
      applySourceRootWrites (sourceExprRootWrites env expression) table := by
  cases expression
  case lit t n =>
    source_writes_finish collectSourceExprRoots.eq_def, sourceExprRootWrites.eq_def; []
  case bool b =>
    source_writes_finish collectSourceExprRoots.eq_def, sourceExprRootWrites.eq_def; []
  case read p =>
    have trace0 := collectSourcePlaceRoots_writes env p
    source_writes_finish collectSourceExprRoots.eq_def, sourceExprRootWrites.eq_def; [trace0]
  case ref m p =>
    have trace0 := collectSourcePlaceRoots_writes env p
    source_writes_finish collectSourceExprRoots.eq_def, sourceExprRootWrites.eq_def; [trace0]
  case slice m v lo hi org =>
    have trace0 := collectSourceViewRoots_writes env v
    have trace1 := collectSourceBoundRoots_writes env lo
    have trace2 := collectSourceBoundRoots_writes env hi
    source_writes_finish collectSourceExprRoots.eq_def, sourceExprRootWrites.eq_def; [trace0, trace1, trace2]
  case len v =>
    have trace0 := collectSourceViewRoots_writes env v
    source_writes_finish collectSourceExprRoots.eq_def, sourceExprRootWrites.eq_def; [trace0]
  case un op e org =>
    have trace0 := collectSourceExprRoots_writes env e
    source_writes_finish collectSourceExprRoots.eq_def, sourceExprRootWrites.eq_def; [trace0]
  case not e =>
    have trace0 := collectSourceExprRoots_writes env e
    source_writes_finish collectSourceExprRoots.eq_def, sourceExprRootWrites.eq_def; [trace0]
  case conv k ty e org =>
    have trace0 := collectSourceExprRoots_writes env e
    source_writes_finish collectSourceExprRoots.eq_def, sourceExprRootWrites.eq_def; [trace0]
  case bin op a b org =>
    have trace0 := collectSourceExprRoots_writes env a
    have trace1 := collectSourceExprRoots_writes env b
    source_writes_finish collectSourceExprRoots.eq_def, sourceExprRootWrites.eq_def; [trace0, trace1]
  case cmp op a b =>
    have trace0 := collectSourceExprRoots_writes env a
    have trace1 := collectSourceExprRoots_writes env b
    source_writes_finish collectSourceExprRoots.eq_def, sourceExprRootWrites.eq_def; [trace0, trace1]
  case and a b =>
    have trace0 := collectSourceExprRoots_writes env a
    have trace1 := collectSourceExprRoots_writes env b
    source_writes_finish collectSourceExprRoots.eq_def, sourceExprRootWrites.eq_def; [trace0, trace1]
  case or a b =>
    have trace0 := collectSourceExprRoots_writes env a
    have trace1 := collectSourceExprRoots_writes env b
    source_writes_finish collectSourceExprRoots.eq_def, sourceExprRootWrites.eq_def; [trace0, trace1]
  case call c args org =>
    have trace0 := collectSourceArgumentRoots_writes env args
    source_writes_finish collectSourceExprRoots.eq_def, sourceExprRootWrites.eq_def; [trace0]
  case push p e org =>
    have trace0 := collectSourcePlaceRoots_writes env p
    have trace1 := collectSourceExprRoots_writes env e
    source_writes_finish collectSourceExprRoots.eq_def, sourceExprRootWrites.eq_def; [trace0, trace1]
  case pop p org =>
    have trace0 := collectSourcePlaceRoots_writes env p
    source_writes_finish collectSourceExprRoots.eq_def, sourceExprRootWrites.eq_def; [trace0]
  case ifE c yes no =>
    have trace0 := collectSourceExprRoots_writes env c
    have trace1 := collectSourceBlockRoots_writes env yes
    have trace2 := collectSourceBlockRoots_writes env no
    source_writes_finish collectSourceExprRoots.eq_def, sourceExprRootWrites.eq_def; [trace0, trace1, trace2]
  case blockE b =>
    have trace0 := collectSourceBlockRoots_writes env b
    source_writes_finish collectSourceExprRoots.eq_def, sourceExprRootWrites.eq_def; [trace0]
  case arrLit ty es =>
    have trace0 := collectSourceExprListRoots_writes env es
    source_writes_finish collectSourceExprRoots.eq_def, sourceExprRootWrites.eq_def; [trace0]
  case structLit ty es =>
    have trace0 := collectSourceExprListRoots_writes env es
    source_writes_finish collectSourceExprRoots.eq_def, sourceExprRootWrites.eq_def; [trace0]
  case fill ty e =>
    have trace0 := collectSourceExprRoots_writes env e
    source_writes_finish collectSourceExprRoots.eq_def, sourceExprRootWrites.eq_def; [trace0]
termination_by sizeOf expression

theorem collectSourcePlaceRoots_writes (env : PEnv) (place : Place) (table : SourceRootTable) :
    (collectSourcePlaceRoots env place table).2 =
      applySourceRootWrites (sourcePlaceRootWrites env place) table := by
  cases place
  case var x =>
    source_writes_finish collectSourcePlaceRoots.eq_def, sourcePlaceRootWrites.eq_def; []
  case global g =>
    source_writes_finish collectSourcePlaceRoots.eq_def, sourcePlaceRootWrites.eq_def; []
  case deref e =>
    have trace0 := collectSourceExprRoots_writes env e
    source_writes_finish collectSourcePlaceRoots.eq_def, sourcePlaceRootWrites.eq_def; [trace0]
  case field p i =>
    have trace0 := collectSourcePlaceRoots_writes env p
    source_writes_finish collectSourcePlaceRoots.eq_def, sourcePlaceRootWrites.eq_def; [trace0]
  case elem v e org =>
    have trace0 := collectSourceViewRoots_writes env v
    have trace1 := collectSourceExprRoots_writes env e
    source_writes_finish collectSourcePlaceRoots.eq_def, sourcePlaceRootWrites.eq_def; [trace0, trace1]
termination_by sizeOf place

theorem collectSourceViewRoots_writes (env : PEnv) (view : View) (table : SourceRootTable) :
    (collectSourceViewRoots env view table).2 =
      applySourceRootWrites (sourceViewRootWrites env view) table := by
  cases view
  case of p =>
    have trace0 := collectSourcePlaceRoots_writes env p
    source_writes_finish collectSourceViewRoots.eq_def, sourceViewRootWrites.eq_def; [trace0]
  case val e =>
    have trace0 := collectSourceExprRoots_writes env e
    source_writes_finish collectSourceViewRoots.eq_def, sourceViewRootWrites.eq_def; [trace0]
termination_by sizeOf view

theorem collectSourceBoundRoots_writes (env : PEnv) (bound : Bound) (table : SourceRootTable) :
    (collectSourceBoundRoots env bound table).2 =
      applySourceRootWrites (sourceBoundRootWrites env bound) table := by
  cases bound
  case omitted =>
    source_writes_finish collectSourceBoundRoots.eq_def, sourceBoundRootWrites.eq_def; []
  case expr e =>
    have trace0 := collectSourceExprRoots_writes env e
    source_writes_finish collectSourceBoundRoots.eq_def, sourceBoundRootWrites.eq_def; [trace0]
  case fromEnd e =>
    have trace0 := collectSourceExprRoots_writes env e
    source_writes_finish collectSourceBoundRoots.eq_def, sourceBoundRootWrites.eq_def; [trace0]
termination_by sizeOf bound

theorem collectSourceArgumentRoots_writes (env : PEnv) (arguments : List Arg) (table : SourceRootTable) :
    (collectSourceArgumentRoots env arguments table).2 =
      applySourceRootWrites (sourceArgumentRootWrites env arguments) table := by
  cases arguments
  case nil =>
    source_writes_finish collectSourceArgumentRoots.eq_def, sourceArgumentRootWrites.eq_def; []
  case cons head rest =>
    cases head
    case byVal e =>
      have trace0 := collectSourceExprRoots_writes env e
      have trace1 := collectSourceArgumentRoots_writes env rest
      source_writes_finish collectSourceArgumentRoots.eq_def, sourceArgumentRootWrites.eq_def; [trace0, trace1]
    case byRef m p =>
      have trace0 := collectSourcePlaceRoots_writes env p
      have trace1 := collectSourceArgumentRoots_writes env rest
      source_writes_finish collectSourceArgumentRoots.eq_def, sourceArgumentRootWrites.eq_def; [trace0, trace1]
termination_by sizeOf arguments

theorem collectSourceExprListRoots_writes (env : PEnv) (expressions : List Expr) (table : SourceRootTable) :
    (collectSourceExprListRoots env expressions table).2 =
      applySourceRootWrites (sourceExprListRootWrites env expressions) table := by
  cases expressions
  case nil =>
    source_writes_finish collectSourceExprListRoots.eq_def, sourceExprListRootWrites.eq_def; []
  case cons e rest =>
    have trace0 := collectSourceExprRoots_writes env e
    have trace1 := collectSourceExprListRoots_writes env rest
    source_writes_finish collectSourceExprListRoots.eq_def, sourceExprListRootWrites.eq_def; [trace0, trace1]
termination_by sizeOf expressions

theorem collectSourceBlockRoots_writes (env : PEnv) (block : Block) (table : SourceRootTable) :
    (collectSourceBlockRoots env block table).2 =
      applySourceRootWrites (sourceBlockRootWrites env block) table := by
  cases block
  case mk scope stmts value =>
    cases value
    case none =>
      have trace0 := collectSourceStmtListRoots_writes ({ env with scopes := scope :: env.scopes }) stmts
      source_writes_finish collectSourceBlockRoots.eq_def, sourceBlockRootWrites.eq_def; [trace0]
    case some e =>
      have trace0 := collectSourceStmtListRoots_writes ({ env with scopes := scope :: env.scopes }) stmts
      have trace1 := collectSourceExprRoots_writes ({ env with scopes := scope :: env.scopes }) e
      source_writes_finish collectSourceBlockRoots.eq_def, sourceBlockRootWrites.eq_def; [trace0, trace1]
termination_by sizeOf block

theorem collectSourceStmtListRoots_writes (env : PEnv) (statements : List Stmt) (table : SourceRootTable) :
    (collectSourceStmtListRoots env statements table).2 =
      applySourceRootWrites (sourceStmtListRootWrites env statements) table := by
  cases statements
  case nil =>
    source_writes_finish collectSourceStmtListRoots.eq_def, sourceStmtListRootWrites.eq_def; []
  case cons statement rest =>
    have trace0 := collectSourceStmtRoots_writes env statement
    have trace1 := collectSourceStmtListRoots_writes env rest
    source_writes_finish collectSourceStmtListRoots.eq_def, sourceStmtListRootWrites.eq_def; [trace0, trace1]
termination_by sizeOf statements

theorem collectSourcePrintRoots_writes (env : PEnv) (arguments : List PrintArg) (table : SourceRootTable) :
    (collectSourcePrintRoots env arguments table).2 =
      applySourceRootWrites (sourcePrintRootWrites env arguments) table := by
  cases arguments
  case nil =>
    source_writes_finish collectSourcePrintRoots.eq_def, sourcePrintRootWrites.eq_def; []
  case cons head rest =>
    cases head
    case text txt =>
      have trace0 := collectSourcePrintRoots_writes env rest
      source_writes_finish collectSourcePrintRoots.eq_def, sourcePrintRootWrites.eq_def; [trace0]
    case expr e =>
      have trace0 := collectSourceExprRoots_writes env e
      have trace1 := collectSourcePrintRoots_writes env rest
      source_writes_finish collectSourcePrintRoots.eq_def, sourcePrintRootWrites.eq_def; [trace0, trace1]
termination_by sizeOf arguments

theorem collectSourceStmtRoots_writes (env : PEnv) (statement : Stmt) (table : SourceRootTable) :
    (collectSourceStmtRoots env statement table).2 =
      applySourceRootWrites (sourceStmtRootWrites env statement) table := by
  cases statement
  case letS x e org =>
    have trace0 := collectSourceExprRoots_writes env e
    source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; [trace0]
  case rebind x e org =>
    have trace0 := collectSourceExprRoots_writes env e
    source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; [trace0]
  case expr e org =>
    have trace0 := collectSourceExprRoots_writes env e
    source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; [trace0]
  case assertS e org =>
    have trace0 := collectSourceExprRoots_writes env e
    source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; [trace0]
  case exit e org =>
    have trace0 := collectSourceExprRoots_writes env e
    source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; [trace0]
  case assign p e org =>
    have trace0 := collectSourcePlaceRoots_writes env p
    have trace1 := collectSourceExprRoots_writes env e
    source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; [trace0, trace1]
  case assignOp op p e org =>
    have trace0 := collectSourcePlaceRoots_writes env p
    have trace1 := collectSourceExprRoots_writes env e
    source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; [trace0, trace1]
  case assignWhole p e org =>
    have trace0 := collectSourcePlaceRoots_writes env p
    have trace1 := collectSourceExprRoots_writes env e
    source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; [trace0, trace1]
  case popN p e org =>
    have trace0 := collectSourcePlaceRoots_writes env p
    have trace1 := collectSourceExprRoots_writes env e
    source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; [trace0, trace1]
  case append p v org =>
    have trace0 := collectSourcePlaceRoots_writes env p
    have trace1 := collectSourceViewRoots_writes env v
    source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; [trace0, trace1]
  case clear p org =>
    have trace0 := collectSourcePlaceRoots_writes env p
    source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; [trace0]
  case «while» c b org =>
    have trace0 := collectSourceExprRoots_writes env c
    have trace1 := collectSourceBlockRoots_writes env b
    source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; [trace0, trace1]
  case forRange x lo hi b org =>
    have trace0 := collectSourceExprRoots_writes env lo
    have trace1 := collectSourceExprRoots_writes env hi
    have trace2 := collectSourceBlockRoots_writes env b
    source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; [trace0, trace1, trace2]
  case forEach x i v byReference b org =>
    have trace0 := collectSourceViewRoots_writes env v
    have trace1 := collectSourceBlockRoots_writes env b
    source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; [trace0, trace1]
  case brk org =>
    source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; []
  case cont org =>
    source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; []
  case abort msg org =>
    source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; []
  case print args org =>
    have trace0 := collectSourcePrintRoots_writes env args
    source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; [trace0]
  case resize p count fill org =>
    cases fill
    case none =>
      have trace0 := collectSourcePlaceRoots_writes env p
      have trace1 := collectSourceExprRoots_writes env count
      source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; [trace0, trace1]
    case some child =>
      have trace0 := collectSourcePlaceRoots_writes env p
      have trace1 := collectSourceExprRoots_writes env count
      have trace2 := collectSourceExprRoots_writes env child
      source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; [trace0, trace1, trace2]
  case ifS c yes no org =>
    cases no
    case none =>
      have trace0 := collectSourceExprRoots_writes env c
      have trace1 := collectSourceBlockRoots_writes env yes
      source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; [trace0, trace1]
    case some child =>
      have trace0 := collectSourceExprRoots_writes env c
      have trace1 := collectSourceBlockRoots_writes env yes
      have trace2 := collectSourceBlockRoots_writes env child
      source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; [trace0, trace1, trace2]
  case ret value org =>
    cases value
    case none =>
      source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; []
    case some child =>
      have trace0 := collectSourceExprRoots_writes env child
      source_writes_finish collectSourceStmtRoots.eq_def, sourceStmtRootWrites.eq_def; [trace0]
termination_by sizeOf statement

end

end Goose.Lower.Validation.SourceCanonicalRootFloors
