import Goose.Core.Roots

namespace Goose.Lower

open Goose.Core

def sourceMappedRoots (arguments : List (List RootRef)) (declared : List RootRef) : List RootRef :=
  declared.foldl (fun roots root => unionRoots roots (match root with
    | .param parameter => arguments[parameter]?.getD []
    | .global global => [.global global]
    | .local _ => [])) []

def sourceCallRoots (env : PEnv) (context : ContextId)
    (arguments : List (List RootRef)) : List RootRef :=
  match env.mod.contexts[context]? with
  | some called => match env.mod.impls[called.impl]? with
    | some impl => match impl.results.toList, called.resultRoots with
      | [type], [declared] => if type.isRefLike then sourceMappedRoots arguments declared else []
      | _, _ => []
    | none => []
  | none => []

def sourceReadRoots (env : PEnv) : Place → List RootRef
  | .var slot =>
    if (env.impl.vars[slot]?).any (·.ty.isRefLike) then (env.ann slot).getD [] else []
  | .deref (.read (.var parameter)) =>
    if env.isRefSliceVar parameter then (env.cont parameter).getD [] else []
  | _ => []

abbrev SourceRootTable := Array (Option (List RootRef))
abbrev SourceRootsM := StateM SourceRootTable

def sourceBlockScope : Block → Nat
  | .mk scope _ _ => scope

mutual

def collectSourceExprRoots (env : PEnv) : Expr → SourceRootsM (List RootRef)
  | .lit .. | .bool .. => pure []
  | .read place => do
    let _ ← collectSourcePlaceRoots env place
    pure (sourceReadRoots env place)
  | .ref _ place => collectSourcePlaceRoots env place
  | .slice _ view lower upper _ => do
    let roots ← collectSourceViewRoots env view
    collectSourceBoundRoots env lower
    collectSourceBoundRoots env upper
    pure roots
  | .len view => do
    let _ ← collectSourceViewRoots env view
    pure []
  | .un _ expression _ | .not expression | .conv _ _ expression _ => do
    let _ ← collectSourceExprRoots env expression
    pure []
  | .bin _ left right _ | .cmp _ left right | .and left right | .or left right => do
    let _ ← collectSourceExprRoots env left
    let _ ← collectSourceExprRoots env right
    pure []
  | .call context arguments _ => do
    pure (sourceCallRoots env context (← collectSourceArgumentRoots env arguments))
  | .push place expression _ => do
    let roots ← collectSourcePlaceRoots env place
    let _ ← collectSourceExprRoots env expression
    pure roots
  | .pop place _ => do
    let _ ← collectSourcePlaceRoots env place
    pure []
  | .ifE condition yes no => do
    let _ ← collectSourceExprRoots env condition
    let yesRoots ← collectSourceBlockRoots env yes
    let noRoots ← collectSourceBlockRoots env no
    let roots := unionRoots yesRoots noRoots
    let scope := sourceBlockScope yes
    modify fun table => if scope < table.size then table.set! scope (some roots) else table
    pure roots
  | .blockE block => collectSourceBlockRoots env block
  | .arrLit _ expressions | .structLit _ expressions => do
    collectSourceExprListRoots env expressions
    pure []
  | .fill _ expression => do
    let _ ← collectSourceExprRoots env expression
    pure []

def collectSourcePlaceRoots (env : PEnv) : Place → SourceRootsM (List RootRef)
  | .var slot => pure [.local slot]
  | .global global => pure [.global global]
  | .deref expression => collectSourceExprRoots env expression
  | .field owner _ => collectSourcePlaceRoots env owner
  | .elem view index _ => do
    let roots ← collectSourceViewRoots env view
    let _ ← collectSourceExprRoots env index
    pure roots

def collectSourceViewRoots (env : PEnv) : View → SourceRootsM (List RootRef)
  | .of place => collectSourcePlaceRoots env place
  | .val expression => collectSourceExprRoots env expression

def collectSourceBoundRoots (env : PEnv) : Bound → SourceRootsM Unit
  | .omitted => pure ()
  | .expr expression | .fromEnd expression => do
    let _ ← collectSourceExprRoots env expression

def collectSourceArgumentRoots (env : PEnv) : List Arg → SourceRootsM (List (List RootRef))
  | [] => pure []
  | .byVal expression :: rest => do
    let roots ← collectSourceExprRoots env expression
    pure (roots :: (← collectSourceArgumentRoots env rest))
  | .byRef _ place :: rest => do
    let roots ← collectSourcePlaceRoots env place
    pure (roots :: (← collectSourceArgumentRoots env rest))

def collectSourceExprListRoots (env : PEnv) : List Expr → SourceRootsM Unit
  | [] => pure ()
  | expression :: rest => do
    let _ ← collectSourceExprRoots env expression
    collectSourceExprListRoots env rest

def collectSourceBlockRoots (env : PEnv) : Block → SourceRootsM (List RootRef)
  | .mk scope statements value => do
    let nested := { env with scopes := scope :: env.scopes }
    collectSourceStmtListRoots nested statements
    match value with
    | some expression => collectSourceExprRoots nested expression
    | none => pure []

def collectSourceStmtListRoots (env : PEnv) : List Stmt → SourceRootsM Unit
  | [] => pure ()
  | statement :: rest => do
    collectSourceStmtRoots env statement
    collectSourceStmtListRoots env rest

def collectSourcePrintRoots (env : PEnv) : List PrintArg → SourceRootsM Unit
  | [] => pure ()
  | .text _ :: rest => collectSourcePrintRoots env rest
  | .expr expression :: rest => do
    let _ ← collectSourceExprRoots env expression
    collectSourcePrintRoots env rest

def collectSourceStmtRoots (env : PEnv) : Stmt → SourceRootsM Unit
  | .letS _ expression _ | .rebind _ expression _ | .expr expression _
  | .assertS expression _ | .exit expression _ => do
    let _ ← collectSourceExprRoots env expression
  | .assign place expression _ | .assignOp _ place expression _
  | .assignWhole place expression _ => do
    let _ ← collectSourcePlaceRoots env place
    let _ ← collectSourceExprRoots env expression
  | .append place view _ => do
    let _ ← collectSourcePlaceRoots env place
    let _ ← collectSourceViewRoots env view
  | .popN place count _ => do
    let _ ← collectSourcePlaceRoots env place
    let _ ← collectSourceExprRoots env count
  | .resize place count fill _ => do
    let _ ← collectSourcePlaceRoots env place
    let _ ← collectSourceExprRoots env count
    match fill with
    | some expression => do
      let _ ← collectSourceExprRoots env expression
    | none => pure ()
  | .clear place _ => do
    let _ ← collectSourcePlaceRoots env place
  | .ifS condition yes no _ => do
    let _ ← collectSourceExprRoots env condition
    let _ ← collectSourceBlockRoots env yes
    match no with
    | some block => do
      let _ ← collectSourceBlockRoots env block
    | none => pure ()
  | .while condition block _ => do
    let _ ← collectSourceExprRoots env condition
    let _ ← collectSourceBlockRoots env block
  | .forRange _ lower upper block _ => do
    let _ ← collectSourceExprRoots env lower
    let _ ← collectSourceExprRoots env upper
    let _ ← collectSourceBlockRoots env block
  | .forEach _ _ view _ block _ => do
    let _ ← collectSourceViewRoots env view
    let _ ← collectSourceBlockRoots env block
  | .ret value _ => match value with
    | some expression => do
      let _ ← collectSourceExprRoots env expression
    | none => pure ()
  | .print arguments _ => collectSourcePrintRoots env arguments
  | .brk .. | .cont .. | .abort .. => pure ()

end

def sourceExprRoots (env : PEnv) (expression : Expr) : List RootRef :=
  (collectSourceExprRoots env expression #[]).1

end Goose.Lower
