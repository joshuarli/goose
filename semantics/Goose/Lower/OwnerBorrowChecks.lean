import Goose.Lower.CoreToGir
import Goose.GIR.Eval

namespace Goose.Lower.OwnerBorrowChecks

open Goose.Core Goose.GIR

private def env (ty : Ty) : TyEnv :=
  { slots := #[], globals := #[], sigs := #[], vals := #[some (.data ty)] }

#guard match (Op.ownerBorrow 0).resultTy (env (.ref .mutable (.grow (.int .i64)))) with
  | .ok ty => ty == .data (.ref .mutable (.grow (.int .i64)))
  | _ => false
#guard match (Op.ownerBorrow 0).resultTy (env (.ref .mutable (.growshrink (.int .i64)))) with
  | .ok ty => ty == .data (.ref .mutable (.growshrink (.int .i64)))
  | _ => false
#guard ((Op.ownerBorrow 0).resultTy (env (.ref .readOnly (.grow (.int .i64))))).isOk == false
#guard ((Op.ownerBorrow 0).resultTy (env (.ref .mutable (.int .i64)))).isOk == false

private def function : Func :=
  { name := "borrow", params := [], results := [], slots := #[], scopes := #[], blocks := #[], summary := .unknown, org := none }

#guard function.permissionOfOp #[] #[] #[] #[(false, true)] 1 (.ownerBorrow 0) == (true, true)
#guard function.permissionOfOp #[] #[] #[] #[(true, false)] 1 (.ownerBorrow 0) == (false, false)
#guard function.permissionOfOp #[] #[] #[] #[(true, true)] 1 (.refFreeze 0) == (false, false)

end Goose.Lower.OwnerBorrowChecks
