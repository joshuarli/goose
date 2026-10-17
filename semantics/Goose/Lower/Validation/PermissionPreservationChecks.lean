import Goose.Lower.CoreToGir
import Goose.GIR.Validate
import Goose.Core.Validate

namespace Goose.Lower.Validation.PermissionChecks

open Goose.Core Goose.GIR

def ownerBorrowReplacement (owner : Ty) (branch : Bool) : Core.Module :=
  let reference := Expr.ref .mutable (.var 0)
  let borrowed := if branch then
      Expr.ifE (.bool true) (.mk 1 [] (some reference)) (.mk 2 [] (some reference))
    else reference
  let main : Impl :=
    { name := "main", params := #[], results := #[],
      vars := #[⟨"owner", owner, .immutable, 0, 0⟩],
      body := .mk 0 [.letS 0 (.arrLit owner []) 0,
        .assignWhole (.deref borrowed) (.arrLit owner []) 0] none,
      summary := .unknown }
  { files := #["owner-borrow.goose"], types := #[], globals := #[], impls := #[main],
    contexts := #[⟨0, "main", [], [], []⟩], entry := 0, origins := #[⟨0, 1, "expr"⟩], profile := .shrink }

def cases : List Core.Module :=
  [ownerBorrowReplacement (.grow (.int .i64)) false,
   ownerBorrowReplacement (.grow (.int .i64)) true,
   ownerBorrowReplacement (.growshrink (.int .i64)) false,
   ownerBorrowReplacement (.growshrink (.int .i64)) true]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
#guard cases.all fun module => (Core.validate module).isOk

def directLetReplacement : Core.Module :=
  let owner := Ty.growshrink (.int .i64)
  let module := ownerBorrowReplacement owner false
  { module with impls := module.impls.modify 0 fun impl =>
      { impl with body := .mk 0 [.letS 0 (.arrLit owner []) 0,
        .assignWhole (.var 0) (.arrLit owner []) 0] none } }

def readonlyBorrowReplacement : Core.Module :=
  let owner := Ty.growshrink (.int .i64)
  let module := ownerBorrowReplacement owner false
  { module with impls := module.impls.modify 0 fun impl =>
      { impl with body := .mk 0 [.letS 0 (.arrLit owner []) 0,
        .assignWhole (.deref (.ref .readOnly (.var 0))) (.arrLit owner []) 0] none } }

#guard match Core.validate directLetReplacement with
  | .error rejection => rejection.rule == .mut
  | _ => false

#guard match Core.validate readonlyBorrowReplacement with
  | .error rejection => rejection.rule == .mut
  | _ => false

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
#guard cases.all fun module => (GIR.validate (lower module)).isOk

end Goose.Lower.Validation.PermissionChecks
