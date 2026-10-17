import Goose.Lower.Validation.CfgGeneratedEdgeHeaders
import Goose.Lower.Validation.ExpressionTypingGenerated

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def CfgSourceExpression (env : Core.TEnv) (results : List Ty) (expr : Expr) : Prop :=
  ∀ {ty : Ty} {start finish : Nat}, Core.tyExpr env expr start = .ok (ty, finish) →
    GeneratedEdgeRun (lowerEnv env.mod env.vars results) none (lowerExpr expr)

def CfgSourcePlace (env : Core.TEnv) (results : List Ty) (place : Place) : Prop :=
  ∀ {info : PlaceInfo} {start finish : Nat}, Core.tyPlace env place start = .ok (info, finish) →
    GeneratedEdgeRun (lowerEnv env.mod env.vars results) none (lowerPlace place)

def CfgSourceView (env : Core.TEnv) (results : List Ty) (view : View) : Prop :=
  ∀ {info : Ty × Bool} {start finish : Nat}, Core.tyView env view start = .ok (info, finish) →
    GeneratedEdgeRun (lowerEnv env.mod env.vars results) none (lowerView view)

def CfgSourceBound (env : Core.TEnv) (results : List Ty) (bound : Bound) : Prop :=
  ∀ {start finish : Nat}, Core.tyBound env bound start = .ok ((), finish) →
    GeneratedEdgeRun (lowerEnv env.mod env.vars results) none (lowerBound bound)

def CfgSourceBlock (env : Core.TEnv) (results : List Ty) (block : Core.Block) : Prop :=
  ∀ {declared : List (VarId × Ty)} {ty : Ty} {start finish : Nat},
    Core.tyBlock env declared block start = .ok (ty, finish) →
    ∀ context pre want, GeneratedEdgeRun (lowerEnv env.mod env.vars results) context (lowerBlock context pre want block)

def CfgSourceStatement (env : Core.TEnv) (results : List Ty) (stmt : Stmt) : Prop :=
  ∀ {output : Core.TEnv} {scope start finish : Nat},
    Core.tyStmt env scope stmt start = .ok (output, finish) →
    ∀ context, GeneratedEdgeRun (lowerEnv env.mod env.vars results) context (lowerStmt context stmt)

def CfgSourceStatements (env : Core.TEnv) (results : List Ty) (stmts : List Stmt) : Prop :=
  ∀ {output : Core.TEnv} {scope start finish : Nat},
    Core.tyStmts env scope stmts start = .ok (output, finish) →
    ∀ context, GeneratedEdgeRun (lowerEnv env.mod env.vars results) context (lowerStmts context stmts)

def CfgSourceExpressions (env : Core.TEnv) (results : List Ty) (exprs : List Expr) : Prop :=
  ∀ {types : List Ty} {start finish : Nat}, Core.tyStructExprs env types exprs start = .ok ((), finish) →
    GeneratedEdgeRun (lowerEnv env.mod env.vars results) none (lowerExprs exprs)

def CfgSourceArguments (env : Core.TEnv) (results : List Ty) (args : List Arg) : Prop :=
  ∀ {callee : Core.Impl} {params : List Param} {start finish : Nat}, params.length = args.length →
    Core.tyArgs env callee params args start = .ok ((), finish) →
    GeneratedEdgeRun (lowerEnv env.mod env.vars results) none (lowerArgs args)

def CfgSourcePrintArguments (env : Core.TEnv) (results : List Ty) (args : List PrintArg) : Prop :=
  ∀ {start finish : Nat}, Core.tyPrintArgs env args start = .ok ((), finish) →
    GeneratedEdgeRun (lowerEnv env.mod env.vars results) none (lowerPrintArgs args)

def CfgSourceEachSource (env : Core.TEnv) (results : List Ty) (view : View) : Prop :=
  ∀ {info : Ty × Bool} {start finish : Nat}, Core.tyView env view start = .ok (info, finish) →
    GeneratedEdgeRun (lowerEnv env.mod env.vars results) none (lowerEachSource view)

end Goose.Lower.Validation
