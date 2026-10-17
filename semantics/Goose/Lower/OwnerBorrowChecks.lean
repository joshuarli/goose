import Goose.Lower.CoreToGir
import Goose.GIR.Eval
import Goose.GIR.Json

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

#guard ({ function with slots := #[⟨.grow (.int .i64), .immutable, 0, 0⟩] }).permissionOfOp
  #[] #[] #[] #[] 0 (.slotAddr 0) == (false, true)
#guard ({ function with slots := #[⟨.growshrink (.int .i64), .immutable, 0, 0⟩] }).permissionOfOp
  #[] #[] #[] #[] 0 (.slotAddr 0) == (false, true)

private def wire : String := (Json.wOp 1 (.ownerBorrow 0)).run {} |>.1

private def tables : Json.Tables :=
  { types := #[], nGlobals := 0, nFuncs := 0, nOrigins := 0,
    nSlots := 0, nScopes := 0, nBlocks := 0 }

#guard wire == "[\"i_owner_borrow\",1,0]"
#guard match Lean.Json.parse wire >>= Json.decInst tables with
  | .ok (.def 1 (.ownerBorrow 0)) => true
  | _ => false
#guard match Lean.Json.parse "[\"i_owner_borrow\",1]" >>= Json.decInst tables with
  | .error _ => true
  | _ => false
#guard match Lean.Json.parse "[\"i_owner_borrow\",1,0,null]" >>= Json.decInst tables with
  | .error _ => true
  | _ => false

theorem ownerBorrow_runtime_identity (cx : FnCtx) (frame : Frame) (owner : ValueId) :
    execPure cx frame (.ownerBorrow owner) = execPure cx frame (.refFreeze owner) := rfl

end Goose.Lower.OwnerBorrowChecks
