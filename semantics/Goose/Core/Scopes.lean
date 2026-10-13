import Goose.Core.Syntax

namespace Goose.Core

mutual

/-- Every block of an expression with the block that encloses it. -/
def exprScopes (parent : Option Nat) : Expr → List (Nat × Option Nat)
  | .lit .. | .bool _ => []
  | .read p => placeScopes parent p
  | .ref _ p => placeScopes parent p
  | .slice _ v lo hi _ => viewScopes parent v ++ boundScopes parent lo ++ boundScopes parent hi
  | .len v => viewScopes parent v
  | .un _ e _ => exprScopes parent e
  | .bin _ a b _ => exprScopes parent a ++ exprScopes parent b
  | .cmp _ a b => exprScopes parent a ++ exprScopes parent b
  | .and a b => exprScopes parent a ++ exprScopes parent b
  | .or a b => exprScopes parent a ++ exprScopes parent b
  | .not e => exprScopes parent e
  | .conv _ _ e _ => exprScopes parent e
  | .call _ args _ => argsScopes parent args
  | .push p e _ => placeScopes parent p ++ exprScopes parent e
  | .pop p _ => placeScopes parent p
  | .ifE c t f => exprScopes parent c ++ blockScopes parent t ++ blockScopes parent f
  | .blockE b => blockScopes parent b
  | .arrLit _ es | .structLit _ es => exprsScopes parent es
  | .fill _ e => exprScopes parent e

def exprsScopes (parent : Option Nat) : List Expr → List (Nat × Option Nat)
  | [] => []
  | e :: rest => exprScopes parent e ++ exprsScopes parent rest

def argsScopes (parent : Option Nat) : List Arg → List (Nat × Option Nat)
  | [] => []
  | .byVal e :: rest => exprScopes parent e ++ argsScopes parent rest
  | .byRef _ p :: rest => placeScopes parent p ++ argsScopes parent rest

def placeScopes (parent : Option Nat) : Place → List (Nat × Option Nat)
  | .var _ | .global _ => []
  | .field p _ => placeScopes parent p
  | .deref e => exprScopes parent e
  | .elem v i _ => viewScopes parent v ++ exprScopes parent i

def viewScopes (parent : Option Nat) : View → List (Nat × Option Nat)
  | .of p => placeScopes parent p
  | .val e => exprScopes parent e

def boundScopes (parent : Option Nat) : Bound → List (Nat × Option Nat)
  | .omitted => []
  | .expr e | .fromEnd e => exprScopes parent e

def blockScopes (parent : Option Nat) : Block → List (Nat × Option Nat)
  | .mk sc stmts value =>
    (sc, parent) :: (stmtsScopes (some sc) stmts ++ (match value with
      | some e => exprScopes (some sc) e
      | none => []))

def stmtsScopes (parent : Option Nat) : List Stmt → List (Nat × Option Nat)
  | [] => []
  | s :: rest => stmtScopes parent s ++ stmtsScopes parent rest

def printScopes (parent : Option Nat) : List PrintArg → List (Nat × Option Nat)
  | [] => []
  | .text _ :: rest => printScopes parent rest
  | .expr e :: rest => exprScopes parent e ++ printScopes parent rest

def stmtScopes (parent : Option Nat) : Stmt → List (Nat × Option Nat)
  | .letS _ e _ => exprScopes parent e
  | .assign p e _ => placeScopes parent p ++ exprScopes parent e
  | .assignOp _ p e _ => placeScopes parent p ++ exprScopes parent e
  | .rebind _ e _ => exprScopes parent e
  | .expr e _ => exprScopes parent e
  | .append p v _ => placeScopes parent p ++ viewScopes parent v
  | .popN p n _ => placeScopes parent p ++ exprScopes parent n
  | .resize p n fill _ => placeScopes parent p ++ exprScopes parent n ++ (match fill with
      | some e => exprScopes parent e
      | none => [])
  | .clear p _ => placeScopes parent p
  | .assignWhole p e _ => placeScopes parent p ++ exprScopes parent e
  | .ifS c t f _ =>
    exprScopes parent c ++ blockScopes parent t ++ (match f with
      | some b => blockScopes parent b
      | none => [])
  | .while c b _ => exprScopes parent c ++ blockScopes parent b
  | .forRange _ lo hi b _ => exprScopes parent lo ++ exprScopes parent hi ++ blockScopes parent b
  | .forEach _ _ v _ b _ => viewScopes parent v ++ blockScopes parent b
  | .ret e _ => (match e with
      | some e => exprScopes parent e
      | none => [])
  | .brk _ | .cont _ => []
  | .print args _ => printScopes parent args
  | .assertS e _ => exprScopes parent e
  | .abort .. => []
  | .exit e _ => exprScopes parent e

end

/-- Scope parents in document-opening order; validation ensures ids match that order. -/
def scopeParents (pairs : List (Nat × Option Nat)) : Array (Option Nat) :=
  pairs.toArray.map Prod.snd

/-- A module's scope sequence must use each dense id at its opening position. -/
def scopeOrderError : List (Nat × Option Nat) → Nat → Option String
  | [], _ => none
  | (scope, parent) :: rest, expected =>
    if scope != expected then some s!"block scope {scope} is not the next scope {expected}"
    else if let some parent := parent then
      if parent < scope then scopeOrderError rest (expected + 1)
      else some s!"block scope {scope} has a parent that is not earlier"
    else scopeOrderError rest (expected + 1)

end Goose.Core
