import Goose.GIR.Validate

namespace Goose.GIR.GlobalRegionTypeChecks

open Goose.Core

private def empty : Func :=
  { name := "main", params := [], results := [], slots := #[], scopes := #[],
    blocks := #[⟨[], [.term (.ret [] none)]⟩], summary := .unknown, org := none }

private def owner : Global :=
  { name := "owner", ty := .grow .bool, kind := .mutable, org := 0,
    init := { empty with
      name := "owner-init"
      results := [.grow .bool]
      blocks := #[⟨[], [.def 0 (.arrLit (.grow .bool) []), .term (.ret [0] (some 0))]⟩] } }

private def header : Global :=
  { name := "header", ty := .slice .readOnly .bool, kind := .mutable, org := 0,
    init := { empty with
      name := "header-init"
      results := [.slice .readOnly .bool]
      blocks := #[⟨[], [.def 0 (.globalAddr 0), .def 1 (.snapshot .owner 0),
        .def 2 (.viewSlice .readOnly 1 .omitted .omitted (some 0)),
        .term (.ret [2] (some 0))]⟩] } }

private def reference : Global :=
  { name := "reference", ty := .ref .mutable (.grow .bool), kind := .immutable, org := 0,
    init := { empty with
      name := "reference-init"
      results := [.ref .mutable (.grow .bool)]
      blocks := #[⟨[], [.def 0 (.globalAddr 0), .term (.ret [0] (some 0))]⟩] } }

private def module (globals : Array Global) : Module :=
  { files := #["global-types"], globals, funcs := #[empty], entry := 0,
    origins := #[⟨0, 1, "global"⟩] }

#guard (validate (module #[owner])).toBool
#guard match validate (module #[owner, header]) with
  | .error rejection => rejection.code == .v010
  | _ => false
#guard match validate (module #[owner, reference]) with
  | .error rejection => rejection.code == .v010
  | _ => false
#guard match validate { module #[owner, header] with entry := 1 } with
  | .error rejection => rejection.code == .v001
  | _ => false

end Goose.GIR.GlobalRegionTypeChecks
