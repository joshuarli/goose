import Goose.Core.Syntax

namespace Goose.Lower.SourceFuelSize

open Goose.Core

mutual

def expr (expression : Expr) : Nat :=
  match expression with
  | .lit _ _ | .bool _ => 1
  | .read place | .ref _ place => 1 + SourceFuelSize.place place
  | .slice _ view low high _ => 1 + SourceFuelSize.view view + boundary low + boundary high
  | .len view => 1 + SourceFuelSize.view view
  | .un _ child _ | .not child | .conv _ _ child _ | .fill _ child => 1 + expr child
  | .bin _ left right _ | .cmp _ left right | .and left right | .or left right => 1 + expr left + expr right
  | .call _ arguments _ => 1 + args arguments
  | .push owner value _ => 1 + place owner + expr value
  | .pop owner _ => 1 + place owner
  | .ifE condition yes no => 1 + expr condition + block yes + block no
  | .blockE body => 1 + block body
  | .arrLit _ expressions | .structLit _ expressions => 1 + exprs expressions
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals omega

def place (place : Place) : Nat :=
  match place with
  | .var _ | .global _ => 1
  | .deref expression => 1 + expr expression
  | .elem view index _ => 1 + SourceFuelSize.view view + expr index
  | .field owner _ => 1 + SourceFuelSize.place owner
termination_by sizeOf place
decreasing_by
  all_goals simp_wf
  all_goals omega

def view (view : View) : Nat :=
  match view with
  | .of owner => 1 + place owner
  | .val expression => 1 + expr expression
termination_by sizeOf view
decreasing_by
  all_goals simp_wf
  all_goals omega

def boundary (bound : Bound) : Nat :=
  match bound with
  | .omitted => 1
  | .expr expression | .fromEnd expression => 1 + expr expression
termination_by sizeOf bound
decreasing_by
  all_goals simp_wf
  all_goals omega

def arg (argument : Arg) : Nat :=
  match argument with
  | .byVal expression => 1 + expr expression
  | .byRef _ owner => 1 + place owner
termination_by sizeOf argument
decreasing_by
  all_goals simp_wf
  all_goals omega

def block (body : Core.Block) : Nat :=
  match body with
  | .mk _ statements value => 1 + stmts statements + optionalExpr value
termination_by sizeOf body
decreasing_by
  all_goals simp_wf
  all_goals omega

def stmt (statement : Stmt) : Nat :=
  match statement with
  | .letS _ expression _ | .rebind _ expression _ | .expr expression _ | .assertS expression _ | .exit expression _ => 1 + expr expression
  | .assign owner expression _ | .assignOp _ owner expression _ | .assignWhole owner expression _ | .popN owner expression _ => 1 + place owner + expr expression
  | .append owner source _ => 1 + place owner + view source
  | .resize owner count fill _ => 1 + place owner + expr count + optionalExpr fill
  | .clear owner _ => 1 + place owner
  | .ifS condition yes no _ => 1 + expr condition + block yes + optionalBlock no
  | .while condition body _ => 1 + expr condition + block body
  | .forRange _ low high body _ => 1 + expr low + expr high + block body
  | .forEach _ _ source _ body _ => 1 + view source + block body
  | .ret value _ => 1 + optionalExpr value
  | .brk _ | .cont _ | .abort _ _ => 1
  | .print arguments _ => 1 + printArgs arguments
termination_by sizeOf statement
decreasing_by
  all_goals simp_wf
  all_goals omega

def stmts (statements : List Stmt) : Nat :=
  match statements with
  | [] => 1
  | head :: tail => 1 + stmt head + stmts tail
termination_by sizeOf statements
decreasing_by
  all_goals simp_wf
  all_goals omega

def exprs (expressions : List Expr) : Nat :=
  match expressions with
  | [] => 1
  | head :: tail => 1 + expr head + exprs tail
termination_by sizeOf expressions
decreasing_by
  all_goals simp_wf
  all_goals omega

def args (arguments : List Arg) : Nat :=
  match arguments with
  | [] => 1
  | head :: tail => 1 + arg head + args tail
termination_by sizeOf arguments
decreasing_by
  all_goals simp_wf
  all_goals omega

def printArgs (arguments : List PrintArg) : Nat :=
  match arguments with
  | [] => 1
  | .text _ :: tail => 1 + printArgs tail
  | .expr expression :: tail => 1 + expr expression + printArgs tail
termination_by sizeOf arguments
decreasing_by
  all_goals simp_wf
  all_goals omega

def optionalExpr (expression : Option Expr) : Nat :=
  match expression with
  | none => 0
  | some expression => 1 + expr expression
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals omega

def optionalBlock (body : Option Core.Block) : Nat :=
  match body with
  | none => 0
  | some body => 1 + block body
termination_by sizeOf body
decreasing_by
  all_goals simp_wf
  all_goals omega

end

end Goose.Lower.SourceFuelSize
