import Goose.Construct.Typing

namespace Goose.Construct
open Goose.Core (V reject VarId)


def Ty.isRefLike : Ty → Bool
  | .ref .. | .slice .. => true
  | _ => false

def Ty.isRefSlice : Ty → Bool
  | .ref _ (.slice ..) => true
  | _ => false


def Place.derefVar? : Place → Option VarId
  | .deref (.read (.var variableId)) => some variableId
  | _ => none

structure AccessEnv where
  mod : Module
  impl : Impl
  ctx : Context

def AccessEnv.declarations (env : AccessEnv) : DeclarationEnv := ⟨env.mod, env.impl.vars⟩

def AccessEnv.placeType? (env : AccessEnv) (place : Place) : Option Ty :=
  env.declarations.placeType? place

def AccessEnv.viewElement? (env : AccessEnv) (view : View) : Option Ty :=
  env.declarations.viewElement? view

def AccessEnv.exprType? (env : AccessEnv) (expression : Expr) : Option Ty :=
  env.declarations.exprType? expression

def AccessEnv.blockType? (env : AccessEnv) (block : Block) : Option Ty :=
  env.declarations.blockType? block


def AccessEnv.variableRoots (env : AccessEnv) (x : VarId) : V (List RootRef) :=
  match (env.ctx.varRoots.find? (·.1 == x)).map (·.2) with
  | some rs => pure rs
  | none => reject .root s!"reference variable {x} has no checked roots"

def AccessEnv.contentRoots (env : AccessEnv) (x : VarId) : V (List RootRef) :=
  match (env.ctx.contentRoots.find? (·.1 == x)).map (·.2) with
  | some rs => pure rs
  | none => reject .root s!"slice-reference variable {x} has no checked content roots"

private def mapExternalRoots (arguments : List (List RootRef)) (roots : List RootRef) : V (List RootRef) := do
  let mut result := []
  for root in roots do
    match root with
    | .static | .global _ => result := result ++ [root]
    | .param position =>
        let some actual := arguments[position]? | reject .call "result root names missing argument"
        result := result ++ actual
    | .local _ => reject .result "callee result names local root"
  pure result.eraseDups

private def mergeRootChannels (left right : List (List RootRef)) : V (List (List RootRef)) := do
  if left.isEmpty then pure right
  else if right.isEmpty then pure left
  else
    if left.length != right.length then reject .result "block result channel count mismatch"
    pure ((left.zip right).map fun (a,b) => (a ++ b).eraseDups)

mutual
def AccessEnv.placeRoots (env : AccessEnv) : Place → V (List RootRef)
  | .var x => pure [.local x]
  | .global g => pure [.global g]
  | .deref e => env.exprRoots e
  | .elem v _ _ => env.viewRoots v
  | .field p _ => env.placeRoots p

def AccessEnv.viewRoots (env : AccessEnv) : View → V (List RootRef)
  | .of p => env.placeRoots p
  | .val e => env.exprRoots e

def AccessEnv.exprRoots (env : AccessEnv) : Expr → V (List RootRef)
  | .read (.var x) => do
    let some t := (env.impl.vars[x]?).map (·.ty) | reject .type "reference read has no variable type"
    if t.isRefLike then env.variableRoots x else pure []
  | .read (.deref (.read (.var x))) => do
    let some t := (env.impl.vars[x]?).map (·.ty) | reject .type "reference read has no variable type"
    if t.isRefSlice then env.contentRoots x else pure []
  | .read _ => pure []
  | .ref _ p => env.placeRoots p
  | .slice _ v _ _ _ => env.viewRoots v
  | .push p _ _ => env.placeRoots p
  | .ifE _ t f _ => do pure ((← env.blockRoots t) ++ (← env.blockRoots f))
  | .blockE b _ => env.blockRoots b
  | .call c args _ => do
    let some ctx := env.mod.contexts[c]? | reject .call "call has no context"
    let roots ← env.argsRoots args
    let mut result := []
    for r in ctx.resultRoots.flatten do
      match r with
      | .static => result := result ++ [.static]
      | .global g => result := result ++ [.global g]
      | .param i =>
        let some rs := roots[i]? | reject .result "call result names a missing argument"
        result := result ++ rs
      | .local _ => reject .result "call result names a local root"
    pure result
  | .bytes (.slice ..) _ _ => pure [.static]
  | .values operands => operands.foldlM (fun found expression => do pure (found ++ (← env.exprRoots expression))) []
  | _ => pure []

def AccessEnv.argRoots (env : AccessEnv) : Arg → V (List RootRef)
  | .byVal e => env.exprRoots e
  | .construct _ => pure []
  | .byRef _ p => env.placeRoots p

def AccessEnv.argsRoots (env : AccessEnv) : List Arg → V (List (List RootRef))
  | [] => pure []
  | a :: args => do pure ((← env.argRoots a) :: (← env.argsRoots args))

def AccessEnv.blockRoots (env : AccessEnv) : Block → V (List RootRef)
  | block => do pure (← env.blockResultRoots block).flatten

def AccessEnv.resultRoots (env : AccessEnv) : Expr → V (List (List RootRef))
  | .call contextId arguments _ => do
      let some context := env.mod.contexts[contextId]? | reject .call "call context outside table"
      let arguments ← env.argsRoots arguments
      context.resultRoots.mapM (mapExternalRoots arguments)
  | .values operands => operands.mapM env.exprRoots
  | .ifE _ left right _ => do
      let a ← env.blockResultRoots left
      let b ← env.blockResultRoots right
      mergeRootChannels a b
  | .blockE block _ => do
      let roots ← env.blockResultRoots block
      if roots.isEmpty then
        let some types := blockResultTypes? 10000 env.declarations block |
          reject .type "cannot determine block result roots"
        pure (types.map fun _ => [])
      else pure roots
  | expression => do pure [← env.exprRoots expression]

def AccessEnv.blockResultRoots (env : AccessEnv) : Block → V (List (List RootRef))
  | .mk _ statements tail => do
      let breaks ← env.statementBreakRoots statements
      let normal ← match tail with | none => pure [] | some expression => env.resultRoots expression
      mergeRootChannels breaks normal

def AccessEnv.statementBreakRoots (env : AccessEnv) : List Stmt → V (List (List RootRef))
  | [] => pure []
  | statement :: rest => do
      let current ← match statement with
        | .breakValue expression _ => env.resultRoots expression
        | .ifS _ (.mk _ left _) right _ => do
            let left ← env.statementBreakRoots left
            let right ← match right with
              | none => pure []
              | some (.mk _ statements _) => env.statementBreakRoots statements
            mergeRootChannels left right
        | .while _ (.mk _ statements _) _ |
          .forRange _ _ _ (.mk _ statements _) _ |
          .forEach _ _ _ _ (.mk _ statements _) _ => env.statementBreakRoots statements
        | _ => pure []
      mergeRootChannels current (← env.statementBreakRoots rest)
end

end Goose.Construct
