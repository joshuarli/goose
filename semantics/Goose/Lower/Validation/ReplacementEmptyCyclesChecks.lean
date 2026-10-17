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


private def cyclicStored : Core.Module :=
  let owner := Ty.growshrink (.int .i64)
  let holder := Ty.ref .mutable (.slice .readOnly (.int .i64))
  { fixture with
    impls := fixture.impls.modify 1 fun impl =>
    { impl with
      params := #[⟨0, .byRef⟩, ⟨1, .byRef⟩],
      vars := #[⟨"q", holder, .immutable, 0, 0⟩, ⟨"r", holder, .immutable, 0, 0⟩,
        ⟨"p", owner, .mutable, 0, 0⟩],
      body := .mk 0 [.assign (.deref (.read (.var 0))) (.read (.deref (.read (.var 1)))) 0,
        .letS 2 (.arrLit owner []) 0,
        .assignWhole (.var 2) (.arrLit owner [.len (.val (.read (.deref (.read (.var 0)))))]) 0] none },
    contexts := fixture.contexts.modify 1 fun context =>
      { context with varRoots := [(0, [.param 0]), (1, [.param 1])], contentRoots := [(0, []), (1, [])] } }
#guard (Core.validate cyclicStored).toBool
#guard (GIR.validate (lower cyclicStored)).toBool
end Goose.Lower.Validation.ReplacementEmptyContentChecks
