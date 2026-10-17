import Goose.Construct.Runtime

namespace Goose.Construct.TypingRuntimeChecks
open Goose.Core (IntTy)

private def module : Module := ⟨#[],#[],#[],#[],#[],0,#[],#[],#[]⟩

private def environment : TypingEnv :=
  { module := module, implementation := none, variables := #[], visible := [],
    scope := 0, loops := 0, globalLimit := 0 }

private def combinedChecks : Bool :=
  (match (typeExpr 8 environment (.not (.bool true))).run 0 with
    | .ok (types,_) => types == [.bool]
    | .error _ => false) &&
  (match (typeExpr 8 environment (.conv .widen (.int .i64) (.lit .u8 7) 0)).run 0 with
    | .ok (types,_) => types == [.int .i64]
    | .error _ => false) &&
  (match expectBool (.bool true) ExecutionState.initial with
    | .ok value _ => value
    | _ => false) &&
  (match expectInt (.int .u8 7) ExecutionState.initial with
    | .ok (ty,value) _ => ty == IntTy.u8 && value == 7
    | _ => false)

example : combinedChecks = true := by cbv

end Goose.Construct.TypingRuntimeChecks
