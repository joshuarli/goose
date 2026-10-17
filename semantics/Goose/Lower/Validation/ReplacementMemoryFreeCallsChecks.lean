import Goose.Lower.CoreToGir
import Goose.Core.Validate
import Goose.GIR.Validate
namespace Goose.Lower.Validation.ReplacementEmptyContentChecks

open Goose Goose.Core Goose.Lower
private def fixture : Core.Module :=
  let owner := Ty.growshrink (.int .i64)
  let receiver : Impl :=
    { name := "replace", params := #[⟨0, .byRef⟩], results := #[],
      vars := #[⟨"q", .ref .readOnly (.slice .readOnly (.int .i64)), .immutable, 0, 0⟩,
        ⟨"p", owner, .mutable, 0, 0⟩],
      body := .mk 0 [.letS 1 (.arrLit owner []) 0,
        .assignWhole (.var 1) (.arrLit owner [.len (.val (.read (.deref (.read (.var 0)))))]) 0] none,
      summary := .unknown }
  let main : Impl :=
    { name := "main", params := #[], results := #[], vars := #[], body := .mk 0 [] none, summary := .unknown }
  { files := #["replacement-empty-content"], types := #[],
    globals := #[],
    impls := #[main, receiver], contexts := #[⟨0, "main", [], [], []⟩,
      ⟨1, "replace", [(0, [.param 0])], [], [(0, [])]⟩],
    entry := 0, origins := #[⟨0, 1, "expr"⟩], profile := .shrink }
#guard (Core.validate fixture).toBool
#guard (GIR.validate (lower fixture)).toBool


private def scalarCall : Core.Module :=
  let owner := Ty.growshrink (.int .i64)
  let receiver : Impl :=
    { name := "replace", params := #[], results := #[], vars := #[⟨"p", owner, .mutable, 0, 0⟩],
      body := .mk 0 [.letS 0 (.arrLit owner []) 0,
        .assignWhole (.var 0) (.arrLit owner [.call 2 [] 0]) 0] none, summary := .unknown }
  let callee : Impl :=
    { name := "scalar", params := #[], results := #[.int .i64], vars := #[],
      body := .mk 0 [] (some (.lit .i64 1)), summary := .unknown }
  { fixture with
    impls := #[{ name := "main", params := #[], results := #[], vars := #[], body := .mk 0 [] none, summary := .unknown }, receiver, callee],
    contexts := #[⟨0, "main", [], [], []⟩, ⟨1, "replace", [], [], []⟩, ⟨2, "scalar", [], [[]], []⟩] }
#guard (Core.validate scalarCall).toBool
#guard (GIR.validate (lower scalarCall)).toBool
private def scalarChain : Core.Module :=
  let leaf : Impl :=
    { name := "leaf", params := #[], results := #[.int .i64], vars := #[],
      body := .mk 0 [] (some (.lit .i64 1)), summary := .unknown }
  { scalarCall with
    impls := (scalarCall.impls.modify 2 fun impl => { impl with body := .mk 0 [] (some (.call 3 [] 0)) }).push leaf,
    contexts := scalarCall.contexts.push ⟨3, "leaf", [], [[]], []⟩ }
private def scalarRecursive : Core.Module :=
  { scalarCall with impls := scalarCall.impls.modify 2 fun impl =>
    { impl with body := .mk 0 [] (some (.ifE (.bool true)
      (.mk 1 [] (some (.lit .i64 1))) (.mk 2 [] (some (.call 2 [] 0))))) } }
#guard (Core.validate scalarChain).toBool
#guard (GIR.validate (lower scalarChain)).toBool
#guard (Core.validate scalarRecursive).toBool
#guard (GIR.validate (lower scalarRecursive)).toBool

private def scalarGlobalRead : Core.Module :=
  { scalarCall with
    globals := #[⟨"other", .int .i64, .immutable, .lit .i64 1, 0⟩],
    impls := scalarCall.impls.modify 2 fun impl =>
      { impl with body := .mk 0 [] (some (.read (.global 0))) } }
private def scalarGlobalWrite : Core.Module :=
  { scalarCall with
    globals := #[⟨"other", .int .i64, .mutable, .lit .i64 1, 0⟩],
    impls := scalarCall.impls.modify 2 fun impl =>
      { impl with body := .mk 0 [.assign (.global 0) (.lit .i64 2) 0] (some (.lit .i64 1)) } }
#guard (Core.validate scalarGlobalRead).toBool
#guard (GIR.validate (lower scalarGlobalRead)).toBool
#guard (Core.validate scalarGlobalWrite).toBool
#guard (GIR.validate (lower scalarGlobalWrite)).toBool

private def genericOwnerScalarCall (write : Bool) : Core.Module :=
  let owner := Ty.growshrink (.int .i64)
  let input := if write then scalarGlobalWrite else scalarGlobalRead
  { input with
    impls := input.impls.modify 1 fun impl =>
      { impl with
        params := #[⟨0, .byRef⟩],
        vars := #[⟨"p", .ref .mutable owner, .immutable, 0, 0⟩],
        body := .mk 0 [.assignWhole (.deref (.read (.var 0))) (.arrLit owner [.call 2 [] 0]) 0] none },
    contexts := input.contexts.modify 1 fun context =>
      { context with varRoots := [(0, [.param 0])] } }
#guard (Core.validate (genericOwnerScalarCall false)).toBool
#guard (Core.validate (genericOwnerScalarCall true)).toBool
#guard (GIR.validate (lower (genericOwnerScalarCall false))).toBool
#guard (GIR.validate (lower (genericOwnerScalarCall true))).toBool

private def genericOwnerDeclaredRead : Core.Module :=
  let input := genericOwnerScalarCall false
  { input with impls := input.impls.modify 2 fun impl =>
    { impl with summary := .known ⟨[.global 0], [], [], [], [], false, false⟩ } }
#guard match Core.validate genericOwnerDeclaredRead with | .error rejection => rejection.rule == .whole | _ => false
#guard match GIR.validate (lower genericOwnerDeclaredRead) with | .error rejection => rejection.code == .v060 | _ => false

private def genericOwnerScalarArgument : Core.Module :=
  let input := genericOwnerScalarCall false
  let owner := Ty.growshrink (.int .i64)
  { input with
    impls := input.impls.modify 1 (fun impl =>
      { impl with body := .mk 0 [.assignWhole (.deref (.read (.var 0)))
          (.arrLit owner [.call 2 [.byRef .readOnly (.global 0)] 0]) 0] none }) |>.modify 2 fun impl =>
      { impl with
        params := #[⟨0, .byRef⟩],
        vars := #[⟨"q", .ref .readOnly (.int .i64), .immutable, 0, 0⟩],
        body := .mk 0 [] (some (.lit .i64 1)) },
    contexts := input.contexts.modify 2 fun context => { context with varRoots := [(0, [.global 0])] } }
#guard match Core.validate genericOwnerScalarArgument with | .error rejection => rejection.rule == .whole | _ => false
#guard (GIR.validate (lower genericOwnerScalarArgument)).toBool

private def separateOwnerScalarArgument : Core.Module :=
  let input := genericOwnerScalarArgument
  let owner := Ty.growshrink (.int .i64)
  { input with
    globals := input.globals.push ⟨"owner", owner, .mutable, .arrLit owner [], 0⟩,
    impls := input.impls.modify 2 fun impl =>
      { impl with summary := .known ⟨[], [], [], [], [], false, false⟩ },
    contexts := input.contexts.modify 1 fun context =>
      { context with varRoots := [(0, [.global 1])] } }

private def genericOwnerGrowArgument : Core.Module :=
  let input := genericOwnerScalarArgument
  let owner := Ty.growshrink (.int .i64)
  { input with
    globals := input.globals.modify 0 fun global =>
      { global with ty := owner, init := .arrLit owner [] },
    impls := input.impls.modify 2 fun impl =>
      { impl with vars := #[⟨"q", .ref .readOnly owner, .immutable, 0, 0⟩] } }

#guard (Core.validate separateOwnerScalarArgument).toBool
#guard (GIR.validate (lower separateOwnerScalarArgument)).toBool
#guard match Core.validate genericOwnerGrowArgument with | .error rejection => rejection.rule == .whole | _ => false
#guard match GIR.validate (lower genericOwnerGrowArgument) with | .error rejection => rejection.code == .v060 | _ => false

end Goose.Lower.Validation.ReplacementEmptyContentChecks
