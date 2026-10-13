import Goose.Core.Validate
import Goose.GIR.Validate
import Goose.Lower.CoreToGir

namespace Goose.Lower.ValidationChecks

open Goose.Core Goose.GIR Goose.Lower

def emptySummary : Core.Summary :=
  { reads := [], writes := [], grows := [], shrinks := [], rebinds := [], aborts := false, outputs := false }

def specializedResult : Core.Module :=
  let f : Core.Impl :=
    { name := "f"
      params := #[⟨0, .byRef⟩, ⟨1, .byRef⟩]
      results := #[.ref .mutable (.int .i64)]
      vars := #[⟨"x", .ref .mutable (.int .i64), .immutable, 0, 0⟩,
        ⟨"y", .ref .mutable (.int .i64), .immutable, 0, 0⟩]
      body := .mk 0 [] (some (.read (.var 0)))
      summary := .known emptySummary }
  let main : Core.Impl :=
    { name := "main"
      params := #[]
      results := #[]
      vars := #[]
      body := .mk 0 [.expr (.call 0 [.byRef .mutable (.global 0), .byRef .mutable (.global 0)] 0) 0] none
      summary := .known emptySummary }
  { files := #["test.goose"]
    types := #[.int .i64, .ref .mutable (.int .i64)]
    globals := #[⟨"g", .int .i64, .mutable, .lit .i64 1, 0⟩]
    impls := #[f, main]
    contexts := #[⟨0, "f", [(0, [.global 0]), (1, [.global 0])], [[.global 0]], []⟩,
      ⟨1, "main", [], [], []⟩]
    entry := 1
    origins := #[⟨0, 1, "test"⟩] }

def orphanUnderstatedSummary : Core.Module :=
  let emptyImpl (name : String) : Core.Impl :=
    { name, params := #[], results := #[], vars := #[], body := .mk 0 [] none,
      summary := .known emptySummary }
  let main := emptyImpl "main"
  let orphan := { emptyImpl "orphan" with body := .mk 0 [.abort "stop" 0] none }
  { files := #["test.goose"]
    types := #[.int .i64]
    globals := #[]
    impls := #[main, orphan]
    contexts := #[⟨0, "main", [], [], []⟩]
    entry := 0
    origins := #[⟨0, 1, "test"⟩] }

#guard match Core.validate specializedResult with
  | .ok _ => true
  | _ => false

#guard match GIR.validate (lower specializedResult) with
  | .ok _ => true
  | _ => false

#guard (lower specializedResult).funcs[0]?.map (·.roots.results) ==
  some #[[.global 0, .param 0, .param 1]]

#guard match Core.validate orphanUnderstatedSummary with
  | .error ⟨.root, _⟩ => true
  | _ => false

#guard match GIR.validate (lower orphanUnderstatedSummary) with
  | .error ⟨.v050, _⟩ => true
  | _ => false

end Goose.Lower.ValidationChecks
