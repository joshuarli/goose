import Goose.Lower.Validation.EmittedTypingSourceResults

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def EmittedSourceExpression (env : Core.TEnv) (results : List Ty) (expr : Expr) : Prop :=
  ∀ {type : Ty} {start finish : Nat}, Core.tyExpr env expr start = .ok (type, finish) →
  ∀ {initial before : LS}, GeneratedBuilderState before →
  EmittedBuilder (lowerEnv env.mod env.vars results) initial before →
  EmittedBuilder (lowerEnv env.mod env.vars results) initial
    (lowerExpr expr (lowerEnv env.mod env.vars results) before).2

def EmittedSourcePlace (env : Core.TEnv) (results : List Ty) (place : Place) : Prop :=
  ∀ {info : PlaceInfo} {start finish : Nat}, Core.tyPlace env place start = .ok (info, finish) →
  ∀ {initial before : LS}, GeneratedBuilderState before →
  EmittedBuilder (lowerEnv env.mod env.vars results) initial before →
  EmittedBuilder (lowerEnv env.mod env.vars results) initial
    (lowerPlace place (lowerEnv env.mod env.vars results) before).2

def EmittedSourceView (env : Core.TEnv) (results : List Ty) (view : View) : Prop :=
  ∀ {element : Ty} {writable : Bool} {start finish : Nat},
  Core.tyView env view start = .ok ((element, writable), finish) →
  ∀ {initial before : LS}, GeneratedBuilderState before →
  EmittedBuilder (lowerEnv env.mod env.vars results) initial before →
  EmittedBuilder (lowerEnv env.mod env.vars results) initial
    (lowerView view (lowerEnv env.mod env.vars results) before).2

end Goose.Lower.Validation
