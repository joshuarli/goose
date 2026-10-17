import Goose.Lower.Validation.StorageWalkActions
import Goose.Lower.Validation.StorageWalkSourceFacts

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def StorageWalkSourceExpression (env : Core.TEnv) (results : List Ty) (stack : List ScopeId) (expr : Expr) : Prop :=
  ∀ {type : Ty} {start finish : Nat}, Core.tyExpr env expr start = .ok (type, finish) →
    StorageWalkVisible env stack → ∀ loop,
      StorageWalkAction (lowerEnv env.mod env.vars results).slots stack loop (lowerExpr expr)

def StorageWalkSourcePlace (env : Core.TEnv) (results : List Ty) (stack : List ScopeId) (place : Place) : Prop :=
  ∀ {info : PlaceInfo} {start finish : Nat}, Core.tyPlace env place start = .ok (info, finish) →
    StorageWalkVisible env stack → ∀ loop,
      StorageWalkAction (lowerEnv env.mod env.vars results).slots stack loop (lowerPlace place)

def StorageWalkSourceView (env : Core.TEnv) (results : List Ty) (stack : List ScopeId) (view : View) : Prop :=
  ∀ {element : Ty} {writable : Bool} {start finish : Nat},
    Core.tyView env view start = .ok ((element, writable), finish) →
    StorageWalkVisible env stack → ∀ loop,
      StorageWalkAction (lowerEnv env.mod env.vars results).slots stack loop (lowerView view)

def StorageWalkSourceEachSource (env : Core.TEnv) (results : List Ty) (stack : List ScopeId) (view : View) : Prop :=
  ∀ {element : Ty} {writable : Bool} {start finish : Nat},
    Core.tyView env view start = .ok ((element, writable), finish) →
    StorageWalkVisible env stack → ∀ loop,
      StorageWalkAction (lowerEnv env.mod env.vars results).slots stack loop (lowerEachSource view)

def StorageWalkSourceBound (env : Core.TEnv) (results : List Ty) (stack : List ScopeId) (bound : Bound) : Prop :=
  ∀ {start finish : Nat}, Core.tyBound env bound start = .ok ((), finish) →
    StorageWalkVisible env stack → ∀ loop,
      StorageWalkAction (lowerEnv env.mod env.vars results).slots stack loop (lowerBound bound)

def StorageWalkSourceArgument (env : Core.TEnv) (results : List Ty) (stack : List ScopeId) : Arg → Prop
  | .byVal expr => StorageWalkSourceExpression env results stack expr
  | .byRef _ place => StorageWalkSourcePlace env results stack place

def StorageWalkSourceStatement (env : Core.TEnv) (results : List Ty) (stack : List ScopeId)
    (scope : ScopeId) (stmt : Stmt) : Prop :=
  ∀ {output : Core.TEnv} {start finish : Nat}, Core.tyStmt env scope stmt start = .ok (output, finish) →
    StorageWalkVisible env stack → scope ∈ stack → ∀ loop,
      StorageWalkAction (lowerEnv env.mod env.vars results).slots stack loop (lowerStmt loop stmt)

def StorageWalkSourceBlock (env : Core.TEnv) (results : List Ty) (stack : List ScopeId) (body : Core.Block) : Prop :=
  ∀ {sourcePre : List (VarId × Ty)} {type : Ty} {start finish : Nat},
    Core.tyBlock env sourcePre body start = .ok (type, finish) →
    StorageWalkVisible env (body.scope :: stack) → ∀ (loop : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool),
      (∀ entry ∈ pre, StorageSlotVisible (lowerEnv env.mod env.vars results).slots (body.scope :: stack) entry.1) →
      StorageWalkAction (lowerEnv env.mod env.vars results).slots stack loop (lowerBlock loop pre want body)

end Goose.Lower.Validation
