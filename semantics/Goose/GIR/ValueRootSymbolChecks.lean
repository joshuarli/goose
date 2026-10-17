import Goose.GIR.Validate

namespace Goose.GIR.ValueRootSymbolChecks

open Goose.Core

private def empty : Func :=
  { name := "empty", params := [], results := [], slots := #[], scopes := #[],
    blocks := #[⟨[], [.term (.ret [] none)]⟩], summary := .unknown, org := none }

private def reference : Func :=
  { empty with
    params := [.ref .readOnly (.int .i64)]
    slots := #[⟨.ref .readOnly (.int .i64), .immutable, 0, 0⟩]
    scopes := #[none]
    blocks := #[⟨[(0, .data (.ref .readOnly (.int .i64)))], [.term (.ret [] none)]⟩] }

private def global : Global :=
  { name := "value", ty := .int .i64, kind := .mutable, org := 0,
    init := { empty with
      results := [.int .i64]
      blocks := #[⟨[], [.def 0 (.constInt .i64 0), .term (.ret [0] (some 0))]⟩] } }

private def module : Module :=
  { files := #["value-root-symbols"], origins := #[⟨0, 1, "value"⟩],
    globals := #[global], funcs := #[empty], entry := 0 }

private def annotated (rows : Array (ValueId × List RootRef)) : Func :=
  { reference with roots := { values := some rows } }

private def symbols (rows : Array (ValueId × List RootRef)) : Bool :=
  (checkSymbols module "reference" (annotated rows)).toBool

#guard symbols #[]
#guard symbols #[(0, [])]
#guard symbols #[(0, [.local 0, .param 0, .global 0])]
#guard !symbols #[(1, [])]
#guard !symbols #[(0, [.local 1])]
#guard !symbols #[(0, [.param 1])]
#guard !symbols #[(0, [.global 1])]
#guard !symbols #[(0, []), (0, [.param 0])]

#guard match validate { module with funcs := #[empty, annotated #[(1, [])]] } with
  | .error rejection => rejection.code == .v001
  | _ => false

#guard match validate { module with globals := #[{ global with
    init := { global.init with roots := { values := some #[(1, [])] } } }] } with
  | .error rejection => rejection.code == .v001
  | _ => false

end Goose.GIR.ValueRootSymbolChecks
