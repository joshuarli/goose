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

end Goose.Lower.Validation.ReplacementEmptyContentChecks
