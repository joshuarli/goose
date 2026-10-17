import Goose.Lower.Validation.SourceValueTypeShapesOperations

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

mutual

def ShapeExprAnnotations (module : Core.Module) : Expr → Prop
  | .lit .. | .bool .. => True
  | .read place | .ref _ place | .pop place _ => ShapePlaceAnnotations module place
  | .slice _ view low high _ => ShapeViewAnnotations module view ∧
      ShapeBoundAnnotations module low ∧ ShapeBoundAnnotations module high
  | .len view => ShapeViewAnnotations module view
  | .un _ expr _ | .not expr | .conv _ _ expr _ => ShapeExprAnnotations module expr
  | .bin _ left right _ | .cmp _ left right | .and left right | .or left right =>
      ShapeExprAnnotations module left ∧ ShapeExprAnnotations module right
  | .call _ args _ => ShapeArgsAnnotations module args
  | .push place expr _ => ShapePlaceAnnotations module place ∧ ShapeExprAnnotations module expr
  | .ifE condition yes no => ShapeExprAnnotations module condition ∧
      ShapeBlockAnnotations module yes ∧ ShapeBlockAnnotations module no
  | .blockE body => ShapeBlockAnnotations module body
  | .arrLit type exprs | .structLit type exprs => type.storable = true ∧
      ShapeExprsAnnotations module exprs
  | .fill type expr => type.storable = true ∧ ShapeExprAnnotations module expr

def ShapeExprsAnnotations (module : Core.Module) : List Expr → Prop
  | [] => True
  | expr :: rest => ShapeExprAnnotations module expr ∧ ShapeExprsAnnotations module rest

def ShapeArgAnnotations (module : Core.Module) : Arg → Prop
  | .byVal expr => ShapeExprAnnotations module expr
  | .byRef _ place => ShapePlaceAnnotations module place

def ShapeArgsAnnotations (module : Core.Module) : List Arg → Prop
  | [] => True
  | arg :: rest => ShapeArgAnnotations module arg ∧ ShapeArgsAnnotations module rest

def ShapePlaceAnnotations (module : Core.Module) : Place → Prop
  | .var .. | .global .. => True
  | .deref expr => ShapeExprAnnotations module expr
  | .field owner _ => ShapePlaceAnnotations module owner
  | .elem view index _ => ShapeViewAnnotations module view ∧ ShapeExprAnnotations module index

def ShapeViewAnnotations (module : Core.Module) : View → Prop
  | .of place => ShapePlaceAnnotations module place
  | .val expr => ShapeExprAnnotations module expr

def ShapeBoundAnnotations (module : Core.Module) : Bound → Prop
  | .omitted => True
  | .expr expr | .fromEnd expr => ShapeExprAnnotations module expr

def ShapeOptionalAnnotations (module : Core.Module) : Option Expr → Prop
  | none => True
  | some expr => ShapeExprAnnotations module expr

def ShapeBlockAnnotations (module : Core.Module) : Core.Block → Prop
  | .mk _ stmts value => ShapeStmtsAnnotations module stmts ∧ ShapeOptionalAnnotations module value

def ShapeStmtsAnnotations (module : Core.Module) : List Stmt → Prop
  | [] => True
  | stmt :: rest => ShapeStmtAnnotations module stmt ∧ ShapeStmtsAnnotations module rest

def ShapePrintAnnotations (module : Core.Module) : List PrintArg → Prop
  | [] => True
  | .text _ :: rest => ShapePrintAnnotations module rest
  | .expr expr :: rest => ShapeExprAnnotations module expr ∧ ShapePrintAnnotations module rest

def ShapeStmtAnnotations (module : Core.Module) : Stmt → Prop
  | .letS _ expr _ | .rebind _ expr _ | .expr expr _ | .assertS expr _ | .exit expr _ =>
      ShapeExprAnnotations module expr
  | .assign place expr _ | .assignOp _ place expr _ | .popN place expr _ | .assignWhole place expr _ =>
      ShapePlaceAnnotations module place ∧ ShapeExprAnnotations module expr
  | .append place view _ => ShapePlaceAnnotations module place ∧ ShapeViewAnnotations module view
  | .resize place size fill _ => ShapePlaceAnnotations module place ∧
      ShapeExprAnnotations module size ∧ ShapeOptionalAnnotations module fill
  | .clear place _ => ShapePlaceAnnotations module place
  | .ifS condition yes no _ => ShapeExprAnnotations module condition ∧
      ShapeBlockAnnotations module yes ∧ match no with
        | none => True
        | some body => ShapeBlockAnnotations module body
  | .while condition body _ => ShapeExprAnnotations module condition ∧ ShapeBlockAnnotations module body
  | .forRange _ low high body _ => ShapeExprAnnotations module low ∧
      ShapeExprAnnotations module high ∧ ShapeBlockAnnotations module body
  | .forEach _ _ view _ body _ => ShapeViewAnnotations module view ∧ ShapeBlockAnnotations module body
  | .ret expr _ => ShapeOptionalAnnotations module expr
  | .print args _ => ShapePrintAnnotations module args
  | .brk .. | .cont .. | .abort .. => True

end

end Goose.Lower.Validation
