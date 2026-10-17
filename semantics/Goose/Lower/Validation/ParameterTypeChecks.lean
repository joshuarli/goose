import Goose.Lower.Validation.Checks

namespace Goose.Lower.Validation.ParameterTypeChecks

open Goose.Core Goose.GIR

private def reference : Ty := .ref .mutable (.int .i64)

private def empty : Func :=
  { name := "empty", params := [], results := [], slots := #[], scopes := #[],
    blocks := #[⟨[], [.term (.ret [] none)]⟩], summary := .unknown, org := none }

private def nestedWriter : Func :=
  { empty with
    name := "nested-writer"
    params := [.ref .mutable reference]
    roots := { params := #[(0, [.param 0])] }
    summary := .known ⟨[.param 0], [], [], [], [], false, false⟩
    blocks := #[⟨[(0, .data (.ref .mutable reference))],
      [.def 1 (.load 0), .def 2 (.constInt .i64 7), .eff (.store 1 2 (some 0)),
        .term (.ret [] (some 0))]⟩] }

private def caller : Func :=
  { empty with
    name := "main"
    slots := #[⟨reference, .mutable, 0, 0⟩]
    scopes := #[none]
    summary := .known ⟨[], [], [], [], [], false, false⟩
    blocks := #[⟨[], [.eff (.enter 0), .def 0 (.globalAddr 0),
      .eff (.slotInit 0 0 (some 0)), .def 1 (.slotAddr 0), .def 2 (.call 1 [1] (some 0)),
      .eff (.leave 0), .term (.ret [] (some 0))]⟩] }

private def global : GIR.Global :=
  { name := "value", ty := .int .i64, kind := .mutable, org := 0,
    init := { empty with
      results := [.int .i64]
      blocks := #[⟨[], [.def 0 (.constInt .i64 0), .term (.ret [0] (some 0))]⟩] } }

private def hiddenGlobalWrite : GIR.Module :=
  { files := #["nested-reference"], funcs := #[caller, nestedWriter], entry := 0,
    globals := #[global], origins := #[⟨0, 1, "store"⟩] }

#guard match GIR.validate hiddenGlobalWrite with
  | .error rejection => rejection.code == .v010
  | _ => false

#guard (Core.validate Checks.parameterSlice).toBool
#guard (GIR.validate (lower Checks.parameterSlice)).toBool

end Goose.Lower.Validation.ParameterTypeChecks
