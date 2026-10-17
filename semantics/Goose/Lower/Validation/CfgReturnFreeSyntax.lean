import Goose.Core.Typing

namespace Goose.Lower.Validation

open Goose.Core

mutual

def ReturnFreeExpr : Expr → Prop
  | .lit .. | .bool .. => True
  | .read place | .ref _ place | .pop place _ => ReturnFreePlace place
  | .slice _ view lo hi _ => ReturnFreeView view ∧ ReturnFreeBound lo ∧ ReturnFreeBound hi
  | .len view => ReturnFreeView view
  | .un _ expr _ | .not expr | .conv _ _ expr _ | .fill _ expr => ReturnFreeExpr expr
  | .bin _ left right _ | .cmp _ left right | .and left right | .or left right =>
      ReturnFreeExpr left ∧ ReturnFreeExpr right
  | .call _ args _ => ReturnFreeArgs args
  | .push place expr _ => ReturnFreePlace place ∧ ReturnFreeExpr expr
  | .ifE condition yes no => ReturnFreeExpr condition ∧ ReturnFreeBlock yes ∧ ReturnFreeBlock no
  | .blockE block => ReturnFreeBlock block
  | .arrLit _ exprs | .structLit _ exprs => ReturnFreeExprs exprs

def ReturnFreeExprs : List Expr → Prop
  | [] => True
  | expr :: rest => ReturnFreeExpr expr ∧ ReturnFreeExprs rest

def ReturnFreeArg : Arg → Prop
  | .byVal expr => ReturnFreeExpr expr
  | .byRef _ place => ReturnFreePlace place

def ReturnFreeArgs : List Arg → Prop
  | [] => True
  | arg :: rest => ReturnFreeArg arg ∧ ReturnFreeArgs rest

def ReturnFreePlace : Place → Prop
  | .var .. | .global .. => True
  | .deref expr => ReturnFreeExpr expr
  | .elem view index _ => ReturnFreeView view ∧ ReturnFreeExpr index
  | .field owner _ => ReturnFreePlace owner

def ReturnFreeView : View → Prop
  | .of place => ReturnFreePlace place
  | .val expr => ReturnFreeExpr expr

def ReturnFreeBound : Bound → Prop
  | .omitted => True
  | .expr expr | .fromEnd expr => ReturnFreeExpr expr

def ReturnFreeValue : Option Expr → Prop
  | none => True
  | some expr => ReturnFreeExpr expr

def ReturnFreeBlock : Block → Prop
  | .mk _ stmts value => ReturnFreeStmts stmts ∧ ReturnFreeValue value

def ReturnFreeStmts : List Stmt → Prop
  | [] => True
  | stmt :: rest => ReturnFreeStmt stmt ∧ ReturnFreeStmts rest

def ReturnFreePrintArgs : List PrintArg → Prop
  | [] => True
  | .text _ :: rest => ReturnFreePrintArgs rest
  | .expr expr :: rest => ReturnFreeExpr expr ∧ ReturnFreePrintArgs rest

def ReturnFreeStmt : Stmt → Prop
  | .letS _ expr _ | .rebind _ expr _ | .expr expr _ | .assertS expr _ | .exit expr _ => ReturnFreeExpr expr
  | .assign place expr _ | .assignOp _ place expr _ | .popN place expr _ |
      .assignWhole place expr _ => ReturnFreePlace place ∧ ReturnFreeExpr expr
  | .append owner view _ => ReturnFreePlace owner ∧ ReturnFreeView view
  | .resize owner size fill _ => ReturnFreePlace owner ∧ ReturnFreeExpr size ∧ ReturnFreeValue fill
  | .clear owner _ => ReturnFreePlace owner
  | .ifS condition yes no _ => ReturnFreeExpr condition ∧ ReturnFreeBlock yes ∧
      match no with | none => True | some block => ReturnFreeBlock block
  | .while condition body _ => ReturnFreeExpr condition ∧ ReturnFreeBlock body
  | .forRange _ lo hi body _ => ReturnFreeExpr lo ∧ ReturnFreeExpr hi ∧ ReturnFreeBlock body
  | .forEach _ _ view _ body _ => ReturnFreeView view ∧ ReturnFreeBlock body
  | .ret .. => False
  | .brk .. | .cont .. | .abort .. => True
  | .print args _ => ReturnFreePrintArgs args

end

mutual

def ReturnFreeStoppingStmt (noReturn : ContextId → Bool) : Stmt → Prop
  | .abort .. => True
  | .exit expr _ => ReturnFreeExpr expr
  | .expr (.call _ args _) _ => ReturnFreeArgs args
  | .ifS condition yes (some no) _ =>
      ReturnFreeExpr condition ∧ ReturnFreeStoppingBlock noReturn yes ∧ ReturnFreeStoppingBlock noReturn no
  | _ => False

def ReturnFreeStoppingBlock (noReturn : ContextId → Bool) : Block → Prop
  | .mk _ stmts _ => ReturnFreeStoppingStmts noReturn stmts

def ReturnFreeStoppingStmts (noReturn : ContextId → Bool) : List Stmt → Prop
  | [] => False
  | stmt :: rest =>
      if stmt.stops noReturn then ReturnFreeStoppingStmt noReturn stmt
      else ReturnFreeStmt stmt ∧ ReturnFreeStoppingStmts noReturn rest

end

end Goose.Lower.Validation
