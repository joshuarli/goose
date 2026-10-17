import Goose.Core.Validate
import Goose.Lower.CoreToGir
import Goose.GIR.Validate

namespace Goose.Lower.Validation.ReplacementContentAdmissionChecks

open Goose.Core Goose.GIR

set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

private def widenedLocal : Core.Module :=
  { files := #["widened-local.goose"], types := #[], globals := #[],
    impls := #[
      { name := "main", params := #[], results := #[], vars := #[],
        body := .mk 0 [.expr (.lit .i64 0) 0] none, summary := .unknown },
      { name := "wrapper", params := #[⟨0,.byRef⟩,⟨1,.byValue⟩,⟨2,.byValue⟩], results := #[],
        vars := #[⟨"holder",.ref .mutable (.slice .mutable .bool),.immutable,0,0⟩,
                  ⟨"a",.slice .mutable .bool,.immutable,0,0⟩,
                  ⟨"b",.slice .mutable .bool,.immutable,0,0⟩,
                  ⟨"wide",.slice .mutable .bool,.immutable,0,0⟩],
        body := .mk 0 [.letS 3 (.read (.var 1)) 0,
          .expr (.call 2 [.byRef .mutable (.deref (.read (.var 0))), .byVal (.read (.var 3))] 0) 0] none,
        summary := .unknown },
      { name := "callee", params := #[⟨0,.byRef⟩,⟨1,.byValue⟩], results := #[],
        vars := #[⟨"holder",.ref .mutable (.slice .mutable .bool),.immutable,0,0⟩,
                  ⟨"value",.slice .mutable .bool,.immutable,0,0⟩],
        body := .mk 0 [] none, summary := .unknown }],
    contexts := #[⟨0,"main",[],[],[]⟩,
      ⟨1,"wrapper",[(0,[.param 0]),(1,[.param 1]),(2,[.param 2]),(3,[.param 1,.param 2])],[],[(0,[.param 1,.param 2])]⟩,
      ⟨2,"callee",[(0,[.param 0]),(1,[.param 1])],[],[(0,[.param 1])]⟩],
    entry := 0, origins := #[⟨0,1,"call"⟩] }

private def widenedLocalReturned : Core.Module :=
  { widenedLocal with
    impls := widenedLocal.impls.set! 2
      { name := "callee", params := #[⟨0,.byRef⟩,⟨1,.byValue⟩], results := #[.slice .mutable .bool],
        vars := #[⟨"holder",.ref .mutable (.slice .mutable .bool),.immutable,0,0⟩,
                  ⟨"value",.slice .mutable .bool,.immutable,0,0⟩],
        body := .mk 0 [] (some (.read (.deref (.read (.var 0))))), summary := .unknown }
    contexts := widenedLocal.contexts.set! 2
      ⟨2,"callee",[(0,[.param 0]),(1,[.param 1])],[[.param 1]],[(0,[.param 1])]⟩ }

private def entryQuery (source : Core.Module) : GIR.ReplacementRootQuery :=
  let module := lower source
  module.funcs[0]?.bind fun func =>
    ((replacementContentFlow module).forFunction func (func.valueTypes module)).value 0

private def fixedGlobalBound : Core.Module :=
  let owner := Ty.grow .bool
  { widenedLocal with
    globals := #[⟨"a", owner, .mutable, .arrLit owner [], 0⟩,
      ⟨"b", owner, .mutable, .arrLit owner [], 0⟩],
    contexts := widenedLocal.contexts.modify 1 (fun context =>
      { context with varRoots := [(0, [.param 0]), (1, [.global 0]), (2, [.global 1]),
          (3, [.global 0, .global 1])], contentRoots := [(0, [.global 0, .global 1])] }) |>.modify 2
      (fun context => { context with varRoots := [(0, [.param 0]), (1, [.global 0])] }) }

private def emptyBound : Core.Module :=
  { widenedLocal with contexts := widenedLocal.contexts.modify 2 fun context =>
    { context with contentRoots := [(0, [])] } }

example : Core.validate widenedLocal = .ok () := by cbv
example : Core.validate widenedLocalReturned = .ok () := by cbv

#guard (GIR.validate (lower widenedLocal)).toBool
#guard entryQuery widenedLocal == some []
#guard (GIR.validate (lower widenedLocalReturned)).toBool
#guard entryQuery widenedLocalReturned == some []
#guard match Core.validate fixedGlobalBound with
  | .error rejection => rejection.rule == .call
  | _ => false
#guard match GIR.validate (lower fixedGlobalBound) with
  | .error rejection => rejection.code == .v050
  | _ => false
#guard match Core.validate emptyBound with
  | .error rejection => rejection.rule == .call
  | _ => false
#guard match GIR.validate (lower emptyBound) with
  | .error rejection => rejection.code == .v050
  | _ => false

end Goose.Lower.Validation.ReplacementContentAdmissionChecks
