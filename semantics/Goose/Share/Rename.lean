import Goose.Core.Syntax

/-!
Renaming the callees of a body.

A call names a context, and a context names the implementation that runs.
Merging implementations therefore changes which context a call should name:
two bodies that differ only in naming two contexts that run one merged
implementation are equal once both contexts are replaced by one of them. `ren*`
applies such a replacement `r` to every call of a body and touches nothing else:
types, operators, origins, variables and places are kept exactly.
-/

namespace Goose.Share

open Goose.Core

/-- A map on the contexts a call may name. -/
abbrev CtxMap := ContextId → ContextId

mutual
def renPlace (r : CtxMap) : Place → Place
  | .var x => .var x
  | .global g => .global g
  | .field p i => .field (renPlace r p) i
  | .deref e => .deref (renExpr r e)
  | .elem v i o => .elem (renView r v) (renExpr r i) o

def renView (r : CtxMap) : View → View
  | .of p => .of (renPlace r p)
  | .val e => .val (renExpr r e)

def renBound (r : CtxMap) : Bound → Bound
  | .expr e => .expr (renExpr r e)
  | .fromEnd e => .fromEnd (renExpr r e)
  | .omitted => .omitted

def renExpr (r : CtxMap) : Expr → Expr
  | .lit t n => .lit t n
  | .bool b => .bool b
  | .read p => .read (renPlace r p)
  | .ref m p => .ref m (renPlace r p)
  | .slice m v lo hi o => .slice m (renView r v) (renBound r lo) (renBound r hi) o
  | .len v => .len (renView r v)
  | .un op e o => .un op (renExpr r e) o
  | .bin op a b o => .bin op (renExpr r a) (renExpr r b) o
  | .cmp op a b => .cmp op (renExpr r a) (renExpr r b)
  | .and a b => .and (renExpr r a) (renExpr r b)
  | .or a b => .or (renExpr r a) (renExpr r b)
  | .not e => .not (renExpr r e)
  | .conv k t e o => .conv k t (renExpr r e) o
  | .call c args o => .call (r c) (renArgs r args) o
  | .push p e o => .push (renPlace r p) (renExpr r e) o
  | .pop p o => .pop (renPlace r p) o
  | .ifE c t f => .ifE (renExpr r c) (renBlock r t) (renBlock r f)
  | .blockE b => .blockE (renBlock r b)
  | .arrLit t es => .arrLit t (renExprs r es)
  | .structLit t es => .structLit t (renExprs r es)
  | .fill t e => .fill t (renExpr r e)

def renExprs (r : CtxMap) : List Expr → List Expr
  | [] => []
  | e :: es => renExpr r e :: renExprs r es

def renArg (r : CtxMap) : Arg → Arg
  | .byVal e => .byVal (renExpr r e)
  | .byRef m p => .byRef m (renPlace r p)

def renArgs (r : CtxMap) : List Arg → List Arg
  | [] => []
  | a :: as => renArg r a :: renArgs r as

def renOptExpr (r : CtxMap) : Option Expr → Option Expr
  | none => none
  | some e => some (renExpr r e)

def renBlock (r : CtxMap) : Block → Block
  | .mk s ss v => .mk s (renStmts r ss) (renOptExpr r v)

def renOptBlock (r : CtxMap) : Option Block → Option Block
  | none => none
  | some b => some (renBlock r b)

def renPrintArg (r : CtxMap) : PrintArg → PrintArg
  | .text s => .text s
  | .expr e => .expr (renExpr r e)

def renPrintArgs (r : CtxMap) : List PrintArg → List PrintArg
  | [] => []
  | a :: as => renPrintArg r a :: renPrintArgs r as

def renStmt (r : CtxMap) : Stmt → Stmt
  | .letS x e o => .letS x (renExpr r e) o
  | .assign p e o => .assign (renPlace r p) (renExpr r e) o
  | .assignOp op p e o => .assignOp op (renPlace r p) (renExpr r e) o
  | .rebind x e o => .rebind x (renExpr r e) o
  | .expr e o => .expr (renExpr r e) o
  | .append p v o => .append (renPlace r p) (renView r v) o
  | .popN p e o => .popN (renPlace r p) (renExpr r e) o
  | .resize p size fill o => .resize (renPlace r p) (renExpr r size) (renOptExpr r fill) o
  | .clear p o => .clear (renPlace r p) o
  | .assignWhole p e o => .assignWhole (renPlace r p) (renExpr r e) o
  | .ifS c t f o => .ifS (renExpr r c) (renBlock r t) (renOptBlock r f) o
  | .while c b o => .while (renExpr r c) (renBlock r b) o
  | .forRange x lo hi b o => .forRange x (renExpr r lo) (renExpr r hi) (renBlock r b) o
  | .forEach x i v byRef b o => .forEach x i (renView r v) byRef (renBlock r b) o
  | .ret e o => .ret (renOptExpr r e) o
  | .brk o => .brk o
  | .cont o => .cont o
  | .print args o => .print (renPrintArgs r args) o
  | .assertS e o => .assertS (renExpr r e) o
  | .abort msg o => .abort msg o
  | .exit e o => .exit (renExpr r e) o

def renStmts (r : CtxMap) : List Stmt → List Stmt
  | [] => []
  | s :: ss => renStmt r s :: renStmts r ss
end

/-- The implementation with every callee of its body renamed. -/
def renImpl (r : CtxMap) (i : Impl) : Impl := { i with body := renBlock r i.body }

/-- The global with every callee of its initializer renamed. -/
def renGlobal (r : CtxMap) (g : Global) : Global := { g with init := renExpr r g.init }

end Goose.Share
