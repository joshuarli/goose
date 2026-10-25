import Goose.Lower.Validation.EmittedMetadataStaticTables

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

mutual

def ResolvedExprAnnotations (module : Core.Module) : Expr → Prop
  | .lit .. | .bool .. => True
  | .read place | .ref _ place | .pop place _ => ResolvedPlaceAnnotations module place
  | .slice _ view low high _ => ResolvedViewAnnotations module view ∧
      ResolvedBoundAnnotations module low ∧ ResolvedBoundAnnotations module high
  | .len view => ResolvedViewAnnotations module view
  | .un _ expr _ | .not expr | .conv _ _ expr _ => ResolvedExprAnnotations module expr
  | .bin _ left right _ | .cmp _ left right | .and left right | .or left right =>
      ResolvedExprAnnotations module left ∧ ResolvedExprAnnotations module right
  | .call _ args _ => ResolvedArgsAnnotations module args
  | .push place expr _ => ResolvedPlaceAnnotations module place ∧ ResolvedExprAnnotations module expr
  | .ifE condition yes no => ResolvedExprAnnotations module condition ∧
      ResolvedBlockAnnotations module yes ∧ ResolvedBlockAnnotations module no
  | .blockE body => ResolvedBlockAnnotations module body
  | .arrLit type exprs | .structLit type exprs => Core.checkResolvedType module type = .ok () ∧
      ResolvedExprsAnnotations module exprs
  | .fill type expr => Core.checkResolvedType module type = .ok () ∧ ResolvedExprAnnotations module expr

def ResolvedExprsAnnotations (module : Core.Module) : List Expr → Prop
  | [] => True
  | expr :: rest => ResolvedExprAnnotations module expr ∧ ResolvedExprsAnnotations module rest

def ResolvedArgAnnotations (module : Core.Module) : Arg → Prop
  | .byVal expr => ResolvedExprAnnotations module expr
  | .byRef _ place => ResolvedPlaceAnnotations module place

def ResolvedArgsAnnotations (module : Core.Module) : List Arg → Prop
  | [] => True
  | arg :: rest => ResolvedArgAnnotations module arg ∧ ResolvedArgsAnnotations module rest

def ResolvedPlaceAnnotations (module : Core.Module) : Place → Prop
  | .var .. | .global .. => True
  | .deref expr => ResolvedExprAnnotations module expr
  | .field owner _ => ResolvedPlaceAnnotations module owner
  | .elem view index _ => ResolvedViewAnnotations module view ∧ ResolvedExprAnnotations module index

def ResolvedViewAnnotations (module : Core.Module) : View → Prop
  | .of place => ResolvedPlaceAnnotations module place
  | .val expr => ResolvedExprAnnotations module expr

def ResolvedBoundAnnotations (module : Core.Module) : Bound → Prop
  | .omitted => True
  | .expr expr | .fromEnd expr => ResolvedExprAnnotations module expr

def ResolvedOptionalAnnotations (module : Core.Module) : Option Expr → Prop
  | none => True
  | some expr => ResolvedExprAnnotations module expr

def ResolvedBlockAnnotations (module : Core.Module) : Core.Block → Prop
  | .mk _ stmts value => ResolvedStmtsAnnotations module stmts ∧ ResolvedOptionalAnnotations module value

def ResolvedStmtsAnnotations (module : Core.Module) : List Stmt → Prop
  | [] => True
  | stmt :: rest => ResolvedStmtAnnotations module stmt ∧ ResolvedStmtsAnnotations module rest

def ResolvedPrintAnnotations (module : Core.Module) : List PrintArg → Prop
  | [] => True
  | .text _ :: rest => ResolvedPrintAnnotations module rest
  | .expr expr :: rest => ResolvedExprAnnotations module expr ∧ ResolvedPrintAnnotations module rest

def ResolvedStmtAnnotations (module : Core.Module) : Stmt → Prop
  | .letS _ expr _ | .rebind _ expr _ | .expr expr _ | .assertS expr _ | .exit expr _ =>
      ResolvedExprAnnotations module expr
  | .assign place expr _ | .assignOp _ place expr _ | .popN place expr _ | .assignWhole place expr _ =>
      ResolvedPlaceAnnotations module place ∧ ResolvedExprAnnotations module expr
  | .append place view _ => ResolvedPlaceAnnotations module place ∧ ResolvedViewAnnotations module view
  | .resize place size fill _ => ResolvedPlaceAnnotations module place ∧
      ResolvedExprAnnotations module size ∧ ResolvedOptionalAnnotations module fill
  | .clear place _ => ResolvedPlaceAnnotations module place
  | .ifS condition yes no _ => ResolvedExprAnnotations module condition ∧
      ResolvedBlockAnnotations module yes ∧ match no with
        | none => True
        | some body => ResolvedBlockAnnotations module body
  | .while condition body _ => ResolvedExprAnnotations module condition ∧ ResolvedBlockAnnotations module body
  | .forRange _ low high body _ => ResolvedExprAnnotations module low ∧
      ResolvedExprAnnotations module high ∧ ResolvedBlockAnnotations module body
  | .forEach _ _ view _ body _ => ResolvedViewAnnotations module view ∧ ResolvedBlockAnnotations module body
  | .ret expr _ => ResolvedOptionalAnnotations module expr
  | .print args _ => ResolvedPrintAnnotations module args
  | .brk .. | .cont .. | .abort .. => True

end

end Goose.Lower.Validation
