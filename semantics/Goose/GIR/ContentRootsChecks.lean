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
    roots := { params := #[(0, [.param 0])], contents := #[(0, [.global 0])] }
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
#guard omitted ({ mod with funcs := mod.funcs.set! 2 { receiver with roots := { params := #[(0, [])], contents := #[(0, [.global 0])] } } })
#guard omitted ({ mod with funcs := mod.funcs.set! 2 { receiver with roots := { params := #[(0, [.param 0])], contents := #[(0, [.param 0])] } } })

private def provenance : Prov := ⟨#[], #[[.param 0]]⟩
#guard mapContentRoots forwarder provenance [0] [.param 0] == [.param 0]
#guard argumentContents forwarder provenance 0 == [.global 0]
#guard mapContentRoots forwarder provenance [0] [.global 0] == [.global 0]
#guard mapContentRoots { forwarder with params := [.ref .mutable backingTy] }
  provenance [0] [.param 0] == [.param 0]

private def localSliceCaller : Func :=
  { forwarder with
    name := "local-slice"
    params := [.ref .mutable backingTy]
    roots := { params := #[(0, [.param 0])] }
    slots := #[⟨.ref .mutable backingTy, .immutable, 0, 0⟩,
      ⟨.slice .mutable (.int .i64), .mutable, 0, 1⟩]
    scopes := #[none]
    blocks := #[⟨[(0, .data (.ref .mutable backingTy))], [
      .eff (.enter 0), .def 1 (.snapshot .borrowed 0),
      .def 2 (.viewSlice .mutable 1 .omitted .omitted (some 0)),
      .eff (.slotInit 1 2 (some 0)), .def 3 (.slotAddr 1),
      .def 4 (.call 2 [3, 0] (some 0)), .eff (.leave 0), .term (.ret [] none)]⟩] }

private def localReceiver : Func :=
  { receiver with
    params := [refSliceTy, .ref .mutable backingTy]
    roots := { params := #[(0, [.param 0]), (1, [.param 1])], contents := #[(0, [.param 1])] }
    blocks := #[⟨[(0, .data refSliceTy), (1, .data (.ref .mutable backingTy))], [.term (.ret [] none)]⟩] }

private def localSliceModule : Module := { mod with funcs := #[empty, localSliceCaller, localReceiver] }
#guard accepted localSliceModule
#guard omitted ({ localSliceModule with funcs := localSliceModule.funcs.set! 2 { localReceiver with roots := { localReceiver.roots with contents := #[(0, [])] } } })
#guard omitted ({ localSliceModule with funcs := localSliceModule.funcs.set! 2 { localReceiver with roots := { localReceiver.roots with contents := #[(0, [.param 0])] } } })

private def globalSliceCaller : Func :=
  { empty with
    name := "global-backed-slice"
    slots := #[⟨.slice .mutable (.int .i64), .mutable, 0, 0⟩]
    scopes := #[none]
    blocks := #[⟨[], [.eff (.enter 0), .def 0 (.globalAddr 0), .def 1 (.snapshot .owner 0),
      .def 2 (.viewSlice .mutable 1 .omitted .omitted (some 0)),
      .eff (.slotInit 0 2 (some 0)), .def 3 (.slotAddr 0),
      .def 4 (.call 2 [3] (some 0)), .eff (.leave 0), .term (.ret [] none)]⟩] }

private def globalSliceModule : Module := { mod with funcs := #[globalSliceCaller, empty, receiver] }
#guard accepted globalSliceModule
#guard omitted ({ globalSliceModule with funcs := globalSliceModule.funcs.set! 2 { receiver with roots := { params := #[(0, [.param 0])], contents := #[(0, [])] } } })
#guard mapContentRoots empty ⟨#[], #[[.global 0]]⟩ [0] [.param 0] == [.global 0]
#guard mapContentRoots { forwarder with params := [.ref .mutable backingTy] }
  ⟨#[], #[[.param 0, .global 0]]⟩ [0] [.param 0] == [.param 0, .global 0]

private def duplicateParameterSlots : Func :=
  { forwarder with
    name := "duplicate-parameter-slots"
    slots := #[⟨refSliceTy, .immutable, 0, 0⟩, ⟨refSliceTy, .immutable, 0, 0⟩]
    scopes := #[none]
    blocks := #[⟨[(0, .data refSliceTy)], [
      .eff (.enter 0), .eff (.slotInit 0 0 (some 0)), .eff (.slotInit 1 0 (some 0)),
      .def 1 (.slotAddr 1), .def 2 (.load 1), .def 3 (.call 2 [2] (some 0)),
      .eff (.leave 0), .term (.ret [] none)]⟩] }

#guard match validate { mod with funcs := #[empty, duplicateParameterSlots, receiver] } with
  | .error e => e.code == .v010
  | .ok () => false

private def singleParameterSlot : Func :=
  { duplicateParameterSlots with
    slots := #[⟨refSliceTy, .immutable, 0, 0⟩]
    blocks := #[⟨[(0, .data refSliceTy)], [
      .eff (.enter 0), .eff (.slotInit 0 0 (some 0)), .def 1 (.slotAddr 0),
      .def 2 (.load 1), .def 3 (.call 2 [2] (some 0)),
      .eff (.leave 0), .term (.ret [] none)]⟩] }

#guard accepted { mod with funcs := #[empty, singleParameterSlot, receiver] }
#guard match validate { mod with funcs := #[{ empty with
    slots := #[⟨.int .i64, .mutable, 0, 7⟩]
    scopes := #[none] }, forwarder, receiver] } with
  | .error e => e.code == .v010
  | .ok () => false

end Goose.GIR.ContentRootsChecks
