import Goose.Core.Syntax

/-!
Boolean equality of Core terms, for the quotient checker.

The syntax types nest `List` and `Option`, which the `DecidableEq` deriving
handler does not accept, so equality is written out here and shown sound in
`Goose.Share.EqualSound`. Every field is compared, including origins and
operand types: two bodies are equal only if they perform the same operations,
checks and aborts, with the same diagnostics.
-/

namespace Goose.Share

open Goose.Core

deriving instance DecidableEq for UnOp, BinOp, CmpOp, ConvKind
deriving instance DecidableEq for Param, LocalVar, Context, Origin

mutual
def eqPlace : Place → Place → Bool
  | .var x, .var y => x == y
  | .global g, .global h => g == h
  | .field p i, .field q j => eqPlace p q && i == j
  | .deref e, .deref f => eqExpr e f
  | .elem v i o, .elem w j p => eqView v w && eqExpr i j && o == p
  | _, _ => false

def eqView : View → View → Bool
  | .of p, .of q => eqPlace p q
  | .val e, .val f => eqExpr e f
  | _, _ => false

def eqBound : Bound → Bound → Bool
  | .expr e, .expr f => eqExpr e f
  | .fromEnd e, .fromEnd f => eqExpr e f
  | .omitted, .omitted => true
  | _, _ => false

def eqExpr : Expr → Expr → Bool
  | .lit t n, .lit u m => t == u && n == m
  | .bool a, .bool b => a == b
  | .read p, .read q => eqPlace p q
  | .ref m p, .ref n q => m == n && eqPlace p q
  | .slice m v lo hi o, .slice n w lo' hi' p =>
    m == n && eqView v w && eqBound lo lo' && eqBound hi hi' && o == p
  | .len v, .len w => eqView v w
  | .un op e o, .un op' f p => op == op' && eqExpr e f && o == p
  | .bin op a b o, .bin op' a' b' p => op == op' && eqExpr a a' && eqExpr b b' && o == p
  | .cmp op a b, .cmp op' a' b' => op == op' && eqExpr a a' && eqExpr b b'
  | .and a b, .and a' b' => eqExpr a a' && eqExpr b b'
  | .or a b, .or a' b' => eqExpr a a' && eqExpr b b'
  | .not e, .not f => eqExpr e f
  | .conv k t e o, .conv k' t' f p => k == k' && t == t' && eqExpr e f && o == p
  | .call c args o, .call d args' p => c == d && eqArgs args args' && o == p
  | .push p e, .push q f => eqPlace p q && eqExpr e f
  | .ifE c t f, .ifE c' t' f' => eqExpr c c' && eqBlock t t' && eqBlock f f'
  | .blockE b, .blockE b' => eqBlock b b'
  | .structLit t es, .structLit u fs => t == u && eqExprs es fs
  | .arrLit t es, .arrLit u fs => t == u && eqExprs es fs
  | .fill t e, .fill u f => t == u && eqExpr e f
  | _, _ => false

def eqExprs : List Expr → List Expr → Bool
  | [], [] => true
  | e :: es, f :: fs => eqExpr e f && eqExprs es fs
  | _, _ => false

def eqArg : Arg → Arg → Bool
  | .byVal e, .byVal f => eqExpr e f
  | .byRef m p, .byRef n q => m == n && eqPlace p q
  | _, _ => false

def eqArgs : List Arg → List Arg → Bool
  | [], [] => true
  | a :: as, b :: bs => eqArg a b && eqArgs as bs
  | _, _ => false

def eqOptExpr : Option Expr → Option Expr → Bool
  | none, none => true
  | some e, some f => eqExpr e f
  | _, _ => false

def eqBlock : Block → Block → Bool
  | .mk s ss v, .mk t ts w => s == t && eqStmts ss ts && eqOptExpr v w

def eqOptBlock : Option Block → Option Block → Bool
  | none, none => true
  | some b, some c => eqBlock b c
  | _, _ => false

def eqPrintArg : PrintArg → PrintArg → Bool
  | .text s, .text t => s == t
  | .expr e, .expr f => eqExpr e f
  | _, _ => false

def eqPrintArgs : List PrintArg → List PrintArg → Bool
  | [], [] => true
  | a :: as, b :: bs => eqPrintArg a b && eqPrintArgs as bs
  | _, _ => false

def eqStmt : Stmt → Stmt → Bool
  | .letS x e o, .letS y f p => x == y && eqExpr e f && o == p
  | .assign q e o, .assign q' f p => eqPlace q q' && eqExpr e f && o == p
  | .assignOp op q e o, .assignOp op' q' f p =>
    op == op' && eqPlace q q' && eqExpr e f && o == p
  | .rebind x e o, .rebind y f p => x == y && eqExpr e f && o == p
  | .expr e o, .expr f p => eqExpr e f && o == p
  | .append q v o, .append q' w p => eqPlace q q' && eqView v w && o == p
  | .ifS c t f o, .ifS c' t' f' p => eqExpr c c' && eqBlock t t' && eqOptBlock f f' && o == p
  | .while c b o, .while c' b' p => eqExpr c c' && eqBlock b b' && o == p
  | .forRange x lo hi b o, .forRange y lo' hi' b' p =>
    x == y && eqExpr lo lo' && eqExpr hi hi' && eqBlock b b' && o == p
  | .forEach x i v byRef b o, .forEach y j w byRef' b' p =>
    x == y && i == j && eqView v w && byRef == byRef' && eqBlock b b' && o == p
  | .ret e o, .ret f p => eqOptExpr e f && o == p
  | .brk o, .brk p => o == p
  | .cont o, .cont p => o == p
  | .print as o, .print bs p => eqPrintArgs as bs && o == p
  | .assertS e o, .assertS f p => eqExpr e f && o == p
  | .abort s o, .abort t p => s == t && o == p
  | .exit e o, .exit f p => eqExpr e f && o == p
  | _, _ => false

def eqStmts : List Stmt → List Stmt → Bool
  | [], [] => true
  | s :: ss, t :: ts => eqStmt s t && eqStmts ss ts
  | _, _ => false
end

def eqSummary (a b : SummaryAnn) : Bool := decide (a = b)

/-- Whole-implementation equality, name included. -/
def eqImpl (a b : Impl) : Bool :=
  a.name == b.name && a.params == b.params && a.results == b.results &&
  a.vars == b.vars && eqBlock a.body b.body && eqSummary a.summary b.summary

/-- Whole-global equality: every field, the initializer compared structurally. -/
def eqGlobal (a b : Global) : Bool :=
  a.name == b.name && a.ty == b.ty && a.kind == b.kind && eqExpr a.init b.init && a.org == b.org

end Goose.Share
