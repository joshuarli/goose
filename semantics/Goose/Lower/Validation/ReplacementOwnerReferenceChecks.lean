import Goose.Lower.CoreToGir
import Goose.Core.Validate
import Goose.GIR.Validate
namespace Goose.Lower.Validation.ReplacementOwnerReferenceChecks

open Goose Goose.Core Goose.Lower
private def ownerReturn (dependent consume : Bool) : Core.Module :=
  let owner := Ty.growshrink (.int .i64)
  let target := if dependent then 0 else 1
  let main : Impl :=
    { name := "main", params := #[], results := #[],
      vars := #[⟨"q", .ref .readOnly owner, .immutable, 1, 0⟩],
      body := .mk 0 [.assignWhole (.global 0)
        (.arrLit owner [.blockE (.mk 1 [.letS 0 (.call 1 [] 0) 0] (some (if consume then .len (.of (.deref (.read (.var 0)))) else .lit .i64 0)))]) 0] none,
      summary := .unknown }
  let callee : Impl :=
    { name := "address", params := #[], results := #[.ref .readOnly owner], vars := #[],
      body := .mk 0 [] (some (.ref .readOnly (.global target))),
      summary := .known ⟨[], [], [], [], [], false, false⟩ }
  { files := #["owner-return"], types := #[],
    globals := #[⟨"p", owner, .mutable, .arrLit owner [], 0⟩,
      ⟨"other", owner, .mutable, .arrLit owner [], 0⟩],
    impls := #[main, callee], contexts := #[⟨0,"main",[(0,[.global target])],[],[]⟩,
      ⟨1,"address",[],[[.global target]],[]⟩], entry := 0,
    origins := #[⟨0,1,"expr"⟩], profile := .shrink }

private def ownerReturnThroughLocal (dependent consume : Bool) : Core.Module :=
  let module := ownerReturn dependent consume
  let target := if dependent then 0 else 1
  let owner := Ty.growshrink (.int .i64)
  { module with
    impls := module.impls.modify 1 fun impl =>
      { impl with
        vars := #[⟨"r", .ref .readOnly owner, .immutable, 0, 0⟩],
        body := .mk 0 [.letS 0 (.ref .readOnly (.global target)) 0] (some (.read (.var 0))) },
    contexts := module.contexts.modify 1 fun context => { context with varRoots := [(0, [.global target])] } }

private def returnedRoots (source : Core.Module) : GIR.ReplacementRootQuery :=
  let module := lower source
  module.funcs[0]?.bind fun func =>
    ((GIR.replacementContentFlow module).forFunction func (func.valueTypes module)).value 1

#guard returnedRoots (ownerReturn true false) == some [.global 0]
#guard returnedRoots (ownerReturnThroughLocal true false) == some [.global 0]

#guard (Core.validate (ownerReturn true false)).toBool
#guard (GIR.validate (lower (ownerReturn true false))).toBool
#guard match Core.validate (ownerReturn true true) with
  | .error rejection => rejection.rule == .whole
  | _ => false
#guard match GIR.validate (lower (ownerReturn true true)) with
  | .error rejection => rejection.code == .v060
  | _ => false
#guard (Core.validate (ownerReturn false false)).toBool
#guard (GIR.validate (lower (ownerReturn false false))).toBool
#guard (Core.validate (ownerReturn false true)).toBool
#guard (GIR.validate (lower (ownerReturn false true))).toBool

#guard (Core.validate (ownerReturnThroughLocal true false)).toBool
#guard (GIR.validate (lower (ownerReturnThroughLocal true false))).toBool
#guard match Core.validate (ownerReturnThroughLocal true true) with
  | .error rejection => rejection.rule == .whole
  | _ => false
#guard match GIR.validate (lower (ownerReturnThroughLocal true true)) with
  | .error rejection => rejection.code == .v060
  | _ => false
#guard (Core.validate (ownerReturnThroughLocal false false)).toBool
#guard (GIR.validate (lower (ownerReturnThroughLocal false false))).toBool
#guard (Core.validate (ownerReturnThroughLocal false true)).toBool
#guard (GIR.validate (lower (ownerReturnThroughLocal false true))).toBool

end Goose.Lower.Validation.ReplacementOwnerReferenceChecks
