import Goose.Lower.Validation.EmittedMetadataStaticProfileSourceHelpers
import Goose.Lower.Validation.SourceStatementTypingBlocks

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def EmittedProfileSourceExpression (env : Core.TEnv) (results : List Ty) (expr : Expr) : Prop :=
  ∀ {type : Ty} {start finish : Nat}, Core.tyExpr env expr start = .ok (type, finish) →
    EmittedProfileRun env.mod.profile (lowerEnv env.mod env.vars results) (lowerExpr expr)

def EmittedProfileSourcePlace (env : Core.TEnv) (results : List Ty) (place : Place) : Prop :=
  ∀ {info : PlaceInfo} {start finish : Nat}, Core.tyPlace env place start = .ok (info, finish) →
    EmittedProfileRun env.mod.profile (lowerEnv env.mod env.vars results) (lowerPlace place)

def EmittedProfileSourceView (env : Core.TEnv) (results : List Ty) (view : View) : Prop :=
  ∀ {element : Ty} {writable : Bool} {start finish : Nat},
    Core.tyView env view start = .ok ((element, writable), finish) →
    EmittedProfileRun env.mod.profile (lowerEnv env.mod env.vars results) (lowerView view)

def EmittedProfileSourceStatement (env : Core.TEnv) (results : List Ty) (scope : ScopeId) (stmt : Stmt) : Prop :=
  ∀ {output : Core.TEnv} {start finish : Nat}, Core.tyStmt env scope stmt start = .ok (output, finish) →
    ∀ loop, EmittedProfileRun env.mod.profile (lowerEnv env.mod env.vars results) (lowerStmt loop stmt)

def EmittedProfileSourceBlock (env : Core.TEnv) (results : List Ty) (body : Core.Block) : Prop :=
  ∀ {sourcePre : List (VarId × Ty)} {type : Ty} {start finish : Nat},
    Core.tyBlock env sourcePre body start = .ok (type, finish) →
    ∀ loop pre want, EmittedProfileRun env.mod.profile (lowerEnv env.mod env.vars results) (lowerBlock loop pre want body)

end Goose.Lower.Validation
