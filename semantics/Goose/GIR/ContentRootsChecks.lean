import Goose.GIR.Validate

namespace Goose.GIR.ContentRootsChecks

open Goose.Core

private def refSliceTy : Ty := .ref .mutable (.slice .mutable (.int .i64))
private def backingTy : Ty := .arr (.int .i64) 2

private def empty : Func :=
  { name := "entry"
    params := []
    results := []
    slots := #[]
    scopes := #[]
    blocks := #[⟨[], [.term (.ret [] none)]⟩]
    summary := .unknown
    org := none }

private def backing : Global :=
  { name := "backing"
    ty := backingTy
    kind := .immutable
    init := { empty with
      name := "backing-init"
      results := [backingTy]
      roots := { results := #[[]] }
      blocks := #[⟨[], [.def 0 (.constInt .i64 1), .def 1 (.constInt .i64 2),
        .def 2 (.arrLit backingTy [0, 1]), .term (.ret [2] (some 0))]⟩] }
    org := 0 }

private def receiver : Func :=
  { empty with
    name := "receiver"
    params := [refSliceTy]
    roots := { params := #[(0, [.param 0])], contents := #[(0, [.param 0])] }
    blocks := #[⟨[(0, .data refSliceTy)], [.term (.ret [] none)]⟩] }

private def forwarder : Func :=
  { receiver with
    name := "forwarder"
    roots := { params := #[(0, [.param 0])], contents := #[(0, [.global 0])] }
    blocks := #[⟨[(0, .data refSliceTy)], [
      .def 1 (.call 2 [0] (some 0)), .term (.ret [] none)]⟩] }

private def mod : Module :=
  { files := #["forwarded-slice"]
    globals := #[backing]
    funcs := #[empty, forwarder, receiver]
    entry := 0
    origins := #[⟨0, 1, "call"⟩] }

private def accepted (m : Module) : Bool := match validate m with
  | .ok () => true
  | .error _ => false

private def omitted (m : Module) : Bool := match validate m with
  | .error e => e.code == .v050
  | .ok () => false

#guard accepted mod
#guard omitted ({ mod with funcs := mod.funcs.set! 2 { receiver with roots := { params := #[(0, [.param 0])], contents := #[(0, [])] } } })
#guard omitted ({ mod with funcs := mod.funcs.set! 2 { receiver with roots := { params := #[(0, [])], contents := #[(0, [.param 0])] } } })

private def provenance : Prov := ⟨#[], #[[.param 0]]⟩
#guard mapContentRoots forwarder provenance [0] [.param 0] == [.global 0]
#guard mapContentRoots forwarder provenance [0] [.global 0] == [.global 0]
#guard mapContentRoots { forwarder with params := [.ref .mutable backingTy] }
  provenance [0] [.param 0] == [.param 0]

end Goose.GIR.ContentRootsChecks
