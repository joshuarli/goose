import Goose.Construct.Typing

namespace Goose.Construct
open Goose.Core (V reject VarId)


def Ty.isRefLike : Ty → Bool
  | .ref .. | .slice .. => true
  | _ => false

def Ty.isRefSlice : Ty → Bool
  | .ref _ (.slice ..) => true
  | _ => false

def Ty.ownerElem? : Ty → Option Ty
  | .grow element | .growshrink element | .limited element _ => some element
  | _ => none

def Place.derefVar? : Place → Option VarId
  | .deref (.read (.var variableId)) => some variableId
  | _ => none

structure AccessEnv where
  mod : Module
  impl : Impl
  ctx : Context

mutual
def AccessEnv.placeType? (env : AccessEnv) : Place → Option Ty
  | .var x => (env.impl.vars[x]?).map (·.ty)
  | .global g => (env.mod.globals[g]?).map (·.ty)
  | .deref e => do
    match ← env.exprType? e with
    | .ref _ t => some t
    | _ => none
  | .elem v _ _ => env.viewElement? v
  | .field p i => do
    match ← env.placeType? p with
    | .structT sid _ => ((← env.mod.structs[sid]?).fields[i]?).map (·.ty)
    | _ => none

def AccessEnv.viewElement? (env : AccessEnv) : View → Option Ty
  | .of p => do
    match ← env.placeType? p with
    | .arr t _ | .varr t | .grow t | .growshrink t | .limited t _ => some t
    | _ => none
  | .val e => do
    match ← env.exprType? e with
    | .slice _ t => some t
    | _ => none

def AccessEnv.exprType? (env : AccessEnv) : Expr → Option Ty
  | .lit t _ => some (.int t)
  | .bool _ | .cmp .. | .and .. | .or .. | .not _ => some .bool
  | .read p => env.placeType? p
  | .ref m p => (env.placeType? p).map (.ref m)
  | .slice m v _ _ _ => (env.viewElement? v).map (.slice m)
  | .len _ => some (.int .i64)
  | .un _ e _ => env.exprType? e
  | .bin _ a _ _ => env.exprType? a
  | .conv _ t _ _ => some t
  | .call c _ _ => do
    let context ← env.mod.contexts[c]?
    let impl ← env.mod.impls[context.impl]?
    match impl.results.toList with
    | [] => some .unit
    | [t] => some t.ty
    | _ => none
  | .push p _ _ => do some (.ref .mutable (← (← env.placeType? p).ownerElem?))
  | .pop p _ => do (← env.placeType? p).ownerElem?
  | .ifE _ t _ => env.blockType? t
  | .blockE b => env.blockType? b
  | .arrLit t _ | .fill t _ | .structLit t _ | .bytes t _ _ | .str t _ _ | .copy t _ _ => some t
  | .resultLocal id _ => (env.impl.vars[id]?).map (·.ty)
  | .values _ => none

def AccessEnv.blockType? (env : AccessEnv) : Block → Option Ty
  | .mk _ _ none => some .unit
  | .mk _ _ (some e) => env.exprType? e
end

def AccessEnv.variableRoots (env : AccessEnv) (x : VarId) : V (List RootRef) :=
  match (env.ctx.varRoots.find? (·.1 == x)).map (·.2) with
  | some rs => pure rs
  | none => reject .root s!"reference variable {x} has no checked roots"

def AccessEnv.contentRoots (env : AccessEnv) (x : VarId) : V (List RootRef) :=
  match (env.ctx.contentRoots.find? (·.1 == x)).map (·.2) with
  | some rs => pure rs
  | none => reject .root s!"slice-reference variable {x} has no checked content roots"

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
  | .ifE _ t f => do pure ((← env.blockRoots t) ++ (← env.blockRoots f))
  | .blockE b => env.blockRoots b
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
  | .mk _ _ none => pure []
  | .mk _ _ (some e) => env.exprRoots e
end
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

mutual
def AccessEnv.resultRoots (env : AccessEnv) : Expr → V (List (List RootRef))
  | .call contextId arguments _ => do
      let some context := env.mod.contexts[contextId]? | reject .call "call context outside table"
      let arguments ← env.argsRoots arguments
      context.resultRoots.mapM (mapExternalRoots arguments)
  | .values operands => operands.mapM env.exprRoots
  | .ifE _ left right => do
      let a ← env.blockResultRoots left
      let b ← env.blockResultRoots right
      if a.length != b.length then reject .result "branch result channel count mismatch"
      pure ((a.zip b).map fun (a,b) => (a ++ b).eraseDups)
  | .blockE block => env.blockResultRoots block
  | expression => do pure [← env.exprRoots expression]

def AccessEnv.blockResultRoots (env : AccessEnv) : Block → V (List (List RootRef))
  | .mk _ _ none => pure []
  | .mk _ _ (some expression) => env.resultRoots expression
end

end Goose.Construct
