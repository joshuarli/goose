import Goose.GIR.Validate

namespace Goose.Lower.Validation.OwnerBorrowChecks

open Goose.Core Goose.GIR

private def owner : Ty := .grow (.int .i64)

private def caller (borrow : Bool) : Func :=
  { name := "main", params := [], results := [],
    slots := #[⟨owner, .immutable, 0, 0⟩], scopes := #[none],
    blocks := #[⟨[],
      [.eff (.enter 0), .def 0 (.arrLit owner []), .eff (.slotInit 0 0 (some 0)),
       .def 1 (.slotAddr 0)] ++
      (if borrow then [.def 2 (.ownerBorrow 1), .def 3 (.call 1 [2] (some 0))]
        else [.def 2 (.call 1 [1] (some 0))]) ++
      [.eff (.leave 0), .term (.ret [] (some 0))]⟩], summary := .unknown, org := none }

private def callee : Func :=
  { name := "take", params := [.ref .mutable owner], results := [], slots := #[], scopes := #[none],
    blocks := #[⟨[(0, .data (.ref .mutable owner))], [.term (.ret [] (some 0))]⟩],
    summary := .unknown, roots := { params := #[(0, [.param 0])] }, org := none }

private def module (profile : ArtifactProfile) (borrow : Bool) : GIR.Module :=
  { files := #["owner-borrow"], globals := #[], funcs := #[caller borrow, callee], entry := 0,
    origins := #[⟨0, 1, "statement"⟩], profile, structs := #[] }

private def accepted (result : Check Unit) : Bool :=
  match result with | .ok () => true | .error _ => false

private def rejected (result : Check Unit) (code : Code) : Bool :=
  match result with | .ok () => false | .error rejection => rejection.code == code

#guard rejected (validate (module .shrink false)) .v030
#guard accepted (validate (module .shrink true))
#guard accepted (validate (module .pilot false))

private def noContents : Func :=
  { name := "forged", params := [], results := [], slots := #[], scopes := #[none],
    blocks := #[⟨[],
      [.def 0 (.refFreeze 0), .def 1 (.ownerBorrow 0), .term (.ret [] none)]⟩], summary := .unknown, org := none }

example : rejected (checkPermissions (module .shrink true) "forged" noContents
    #[some (.data (.ref .mutable owner)), some (.data (.ref .mutable owner))]) .v030 = true := by decide

private def typeEnv (ty : Ty) : TyEnv :=
  { vals := #[some (.data ty)], slots := #[], globals := #[], sigs := #[], profile := .shrink }

#guard !((Op.ownerBorrow 0).resultTy (typeEnv (.ref .readOnly owner))).toBool
#guard !((Op.ownerBorrow 0).resultTy (typeEnv (.ref .mutable (.arr (.int .i64) 1)))).toBool

end Goose.Lower.Validation.OwnerBorrowChecks
