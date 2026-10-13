import Goose.Lower.Commands

namespace Goose.GIR.StructChecks

open Goose.Core

private def descriptor : StructDef :=
  { byteSize := 9
    fields := #[⟨.int .u8, .immutable, .mutable, 0⟩,
      ⟨.int .i64, .mutable, .mutable, 1⟩] }

private def recordTy : Ty := .structT 0 (.cons (.int .u8) (.cons (.int .i64) .nil))

private def body : List Inst := [
  .eff (.enter 0),
  .def 0 (.constInt .u8 1), .def 1 (.constInt .i64 42),
  .def 2 (.structLit recordTy [0, 1]), .eff (.slotInit 0 2 (some 0)),
  .def 3 (.slotAddr 0), .def 4 (.load 3), .eff (.slotInit 1 4 (some 0)),
  .def 5 (.fieldAddr 3 1), .def 6 (.constInt .i64 99), .eff (.store 5 6 (some 0)),
  .def 7 (.slotAddr 1), .def 8 (.fieldAddr 7 1), .def 9 (.load 8),
  .def 10 (.load 5), .def 11 (.fieldAddr 3 0), .def 12 (.load 11),
  .eff (.print [.val 9, .text ",", .val 10, .text ",", .val 12] (some 0)),
  .eff (.leave 0), .term (.ret [] none)]

private def fn : Func :=
  { name := "struct-copy"
    params := []
    results := []
    slots := #[⟨recordTy, .immutable, 0, 0⟩, ⟨recordTy, .immutable, 0, 1⟩]
    scopes := #[none]
    blocks := #[⟨[], body⟩]
    summary := .unknown
    org := some 0 }

private def mod : Module :=
  { files := #["struct"]
    globals := #[]
    funcs := #[fn]
    entry := 0
    origins := #[⟨0, 1, "print"⟩]
    profile := .shrink
    structs := #[descriptor] }

private def accepted (m : Module) : Bool := match validate m with
  | .ok () => true
  | .error _ => false

private def rejected (m : Module) (code : Code) : Bool := match validate m with
  | .ok () => false
  | .error e => e.code == code

private def changeInst (index : Nat) (i : Inst) : Module :=
  { mod with funcs := #[{ fn with blocks := #[⟨[], body.set index i⟩] }] }

#guard accepted mod
private def ran (m : Module) (trace : String) : Bool := match run 100 .release m with
  | .done .returned output => output == trace
  | _ => false

#guard ran mod "42,99,1\n"
#guard rejected (changeInst 3 (.def 2 (.structLit recordTy [0]))) .v010
#guard rejected (changeInst 3 (.def 2 (.structLit recordTy [1, 0]))) .v010
#guard rejected (changeInst 8 (.def 5 (.fieldAddr 3 2))) .v010
#guard rejected (changeInst 8 (.def 5 (.fieldAddr 3 0))) .v010
#guard rejected (changeInst 10 (.eff (.store 11 0 (some 0)))) .v020
#guard rejected ({ mod with structs := #[{ descriptor with fields := descriptor.fields.set! 1 ⟨.int .i64, .immutable, .mutable, 1⟩ }] }) .v030
#guard accepted ({ mod with structs := #[{ descriptor with fields := descriptor.fields.set! 1 ⟨.int .i64, .mutable, .readOnly, 1⟩ }] })
#guard rejected ({ mod with structs := #[{ descriptor with byteSize := 8 }] }) .v010
#guard rejected ({ mod with structs := #[{ descriptor with fields := descriptor.fields.set! 1 ⟨.int .i64, .mutable, .mutable, 0⟩ }] }) .v010

private def wire : String := Json.write mod
#guard match Json.decodeBytes wire.toUTF8 with
  | .error _ => false
  | .ok m => accepted m && Json.write m == wire && ran m "42,99,1\n"

private def parsedWire : Lean.Json := (Lean.Json.parse wire).toOption.getD .null
private def moduleFields : Array Lean.Json := match parsedWire with
  | .arr xs => xs
  | _ => #[]
private def malformed (xs : Array Lean.Json) : Bool := match Json.decodeModule (.arr xs) with
  | .error _ => true
  | .ok _ => false

#guard malformed (moduleFields.set! 2 (.str "core-pilot"))
#guard malformed (moduleFields.extract 0 5 ++ moduleFields.extract 6 moduleFields.size)
#guard malformed (moduleFields.push (.arr #[]))
#guard malformed (moduleFields.set! 4 (.arr #[.arr #[.str "struct", .num 1]]))
#guard malformed (moduleFields.set! 5 (.arr #[]))

private def withExtra (extra : Func) : Module := { mod with funcs := #[fn, extra] }

private def borrowed : Func :=
  { fn with
    name := "borrowed"
    params := [.ref .readOnly recordTy]
    slots := #[]
    scopes := #[]
    blocks := #[⟨[(0, .data (.ref .readOnly recordTy))], [
      .def 1 (.fieldAddr 0 1), .def 2 (.constInt .i64 7),
      .eff (.store 1 2 (some 0)), .term (.ret [] none)]⟩] }

#guard rejected (withExtra borrowed) .v030
#guard accepted (withExtra { borrowed with blocks := #[⟨[(0, .data (.ref .readOnly recordTy))], [
  .def 1 (.fieldAddr 0 1), .def 2 (.load 1),
  .eff (.print [.val 2] (some 0)), .term (.ret [] none)]⟩] })

private def joined : Func :=
  { fn with
    name := "permission-join"
    slots := #[⟨recordTy, .immutable, 0, 0⟩]
    blocks := #[⟨[], [
      .eff (.enter 0), .def 0 (.constInt .u8 1), .def 1 (.constInt .i64 42),
      .def 2 (.structLit recordTy [0, 1]), .eff (.slotInit 0 2 (some 0)),
      .def 3 (.slotAddr 0), .def 4 (.refFreeze 3), .def 5 (.constBool true),
      .term (.condbr 5 1 [3] 1 [4])]⟩,
      ⟨[(6, .data (.ref .readOnly recordTy))], [
        .def 7 (.fieldAddr 6 1), .def 8 (.constInt .i64 7),
        .eff (.store 7 8 (some 0)), .eff (.leave 0), .term (.ret [] none)]⟩] }

#guard rejected (withExtra joined) .v030
#guard accepted (withExtra { joined with blocks := joined.blocks.modify 0 fun b =>
  { b with insts := b.insts.set 8 (.term (.br 1 [3])) } })

private def nestedTy : Ty := .structT 1 (.cons recordTy .nil)
private def nestedDescriptor (contents : Mutability) : StructDef :=
  { byteSize := 9, fields := #[⟨recordTy, .immutable, contents, 0⟩] }
private def nested : Func :=
  { fn with
    name := "nested-permissions"
    slots := #[⟨nestedTy, .immutable, 0, 0⟩]
    blocks := #[⟨[], [
      .eff (.enter 0), .def 0 (.constInt .u8 1), .def 1 (.constInt .i64 42),
      .def 2 (.structLit recordTy [0, 1]), .def 3 (.structLit nestedTy [2]),
      .eff (.slotInit 0 3 (some 0)), .def 4 (.slotAddr 0),
      .def 5 (.fieldAddr 4 0), .def 6 (.fieldAddr 5 1), .def 7 (.constInt .i64 7),
      .eff (.store 6 7 (some 0)), .eff (.leave 0), .term (.ret [] none)]⟩] }

#guard accepted ({ withExtra nested with structs := #[descriptor, nestedDescriptor .mutable] })
#guard rejected ({ withExtra nested with structs := #[descriptor, nestedDescriptor .readOnly] }) .v030
#guard rejected ({ mod with structs := #[descriptor, descriptor], funcs := #[{ fn with
  blocks := #[⟨[], body.set 3 (.def 2 (.structLit (.structT 1 (.cons (.int .u8) (.cons (.int .i64) .nil))) [0, 1]))⟩] }] }) .v010

private def core : Core.Module :=
  { files := mod.files
    types := #[recordTy]
    globals := #[]
    impls := #[{
      name := "lower-struct"
      params := #[]
      results := #[]
      vars := #[⟨"s", recordTy, .immutable, 0, 0⟩]
      body := .mk 0 [
        .letS 0 (.structLit recordTy [.lit .u8 1, .lit .i64 42]) 0,
        .assign (.field (.var 0) 1) (.lit .i64 99) 0,
        .print [.expr (.read (.field (.var 0) 1))] 0] none
      summary := .unknown }]
    contexts := #[{ impl := 0, decl := "lower-struct", varRoots := [], resultRoots := [] }]
    entry := 0
    origins := mod.origins
    profile := .shrink
    structs := mod.structs }

#guard accepted (Goose.Lower.lower core)
#guard ran (Goose.Lower.lower core) "99\n"
#guard (Goose.Lower.lower core).structs == core.structs
#guard (Goose.Lower.lower core).profile == .shrink

private def effectfulInitializer (scope : Nat) (text : String) (stop : Bool) : Expr :=
  .blockE (.mk scope ([.print [.text text] 0] ++
    if stop then [.abort "stop" 0] else []) (some (.lit .i64 scope)))

private def initializerCore (stop : Bool) : Core.Module :=
  match core.impls[0]? with
  | none => core
  | some impl =>
    let t := Ty.structT 0 (.cons (.int .i64) (.cons (.int .i64) (.cons (.int .i64) .nil)))
    { core with
      types := #[t]
      structs := #[{ byteSize := 24, fields := #[
        ⟨.int .i64, .mutable, .mutable, 0⟩, ⟨.int .i64, .mutable, .mutable, 8⟩,
        ⟨.int .i64, .mutable, .mutable, 16⟩] }]
      impls := #[{ impl with
        vars := #[⟨"s", t, .immutable, 0, 0⟩]
        body := .mk 0 [.letS 0 (.structLit t [
          effectfulInitializer 1 "a" false, effectfulInitializer 2 "b" stop,
          effectfulInitializer 3 "c" false]) 0] none }] }
#guard accepted (Goose.Lower.lower (initializerCore false))
#guard ran (Goose.Lower.lower (initializerCore false)) "a\nb\nc\n"
#guard accepted (Goose.Lower.lower (initializerCore true))
#guard match run 100 .release (Goose.Lower.lower (initializerCore true)) with
  | .done (.aborted .userAbort 0) trace => trace == "a\nb\n"
  | _ => false

private def writeSummary : Func :=
  { borrowed with
    params := [.ref .mutable recordTy]
    summary := .known ⟨[], [], [], [], false, false⟩
    blocks := #[⟨[(0, .data (.ref .mutable recordTy))], [
      .def 1 (.fieldAddr 0 1), .def 2 (.constInt .i64 7),
      .eff (.store 1 2 (some 0)), .term (.ret [] none)]⟩] }

#guard rejected (withExtra writeSummary) .v050
#guard accepted (withExtra { writeSummary with summary := .known ⟨[], [.param 0], [], [], false, false⟩ })

private def emptyModule (profile : ArtifactProfile) : Module :=
  { mod with
    profile
    structs := #[]
    funcs := #[{ fn with
      slots := #[]
      scopes := #[]
      org := none
      blocks := #[⟨[], [.term (.ret [] none)]⟩] }] }

#guard match Json.decodeBytes (Json.write (emptyModule .shrink)).toUTF8 with
  | .ok m => accepted m && m.structs.isEmpty && m.profile == .shrink
  | .error _ => false
#guard match Json.decodeBytes (Json.write (emptyModule .pilot)).toUTF8 with
  | .ok m => accepted m && m.structs.isEmpty && m.profile == .pilot
  | .error _ => false
#guard match Json.decodeBytes (Json.write { emptyModule .pilot with funcs := #[{
    fn with slots := #[], scopes := #[], blocks := #[⟨[], [
      .def 0 (.structLit (.int .i64) []), .term (.ret [] none)]⟩] }] }).toUTF8 with
  | .error _ => true
  | .ok _ => false

private def arrayFieldCore (binding : VarKind) (contents : Mutability) (write : Bool) : Core.Module :=
  match core.impls[0]? with
  | none => core
  | some impl =>
    let arrayTy := Ty.arr (.int .i64) 2
    let structTy := Ty.structT 0 (.cons arrayTy .nil)
    let element := Place.elem (.of (.field (.var 0) 0)) (.lit .i64 1) 0
    { core with
      types := #[structTy]
      structs := #[{ byteSize := 16, fields := #[⟨arrayTy, binding, contents, 0⟩] }]
      impls := #[{ impl with
        vars := #[⟨"s", structTy, .immutable, 0, 0⟩]
        body := .mk 0 ([
          .letS 0 (.structLit structTy [.arrLit arrayTy [.lit .i64 1, .lit .i64 2]]) 0] ++
          (if write then [.assign element (.lit .i64 9) 0] else []) ++
          [.print [.expr (.read element)] 0]) none }] }

#guard accepted (Goose.Lower.lower (arrayFieldCore .immutable .mutable true))
#guard ran (Goose.Lower.lower (arrayFieldCore .immutable .mutable true)) "9\n"
#guard accepted (Goose.Lower.lower (arrayFieldCore .mutable .readOnly false))
#guard ran (Goose.Lower.lower (arrayFieldCore .mutable .readOnly false)) "2\n"
#guard rejected (Goose.Lower.lower (arrayFieldCore .mutable .readOnly true)) .v030
#guard match Core.validate (arrayFieldCore .immutable .mutable true) with
  | .ok () => true
  | .error _ => false
#guard match Core.validate (arrayFieldCore .mutable .readOnly false) with
  | .ok () => true
  | .error _ => false

private def borrowedArray (mode : SnapshotMode) (write : Bool) : Module :=
  let arrayTy := Ty.arr (.int .i64) 2
  let structTy := Ty.structT 0 (.cons arrayTy .nil)
  let refTy := Ty.ref .readOnly structTy
  let extra : Func :=
    { borrowed with
      params := [refTy]
      blocks := #[⟨[(0, .data refTy)], [
        .def 1 (.fieldAddr 0 0), .def 2 (.snapshot mode 1),
        .def 3 (.constInt .i64 1), .def 4 (.indexChecked 2 3 (some 0)),
        .def 5 (.load 4)] ++
        (if write then [.eff (.store 4 5 (some 0))] else []) ++
        [.eff (.print [.val 5] (some 0)), .term (.ret [] none)]⟩] }
  { emptyModule .shrink with
    structs := #[{ byteSize := 16, fields := #[⟨arrayTy, .immutable, .mutable, 0⟩] }]
    funcs := (emptyModule .shrink).funcs.push extra }

#guard accepted (borrowedArray .borrowed false)
#guard accepted (borrowedArray .owner false)
#guard rejected (borrowedArray .borrowed true) .v030
#guard rejected (borrowedArray .owner true) .v030
#guard match (borrowedArray .borrowed false).funcs[1]? with
  | some f => (f.valueTypes (borrowedArray .borrowed false))[2]? == some (some (.view .readOnly (.int .i64)))
  | none => false

private def fieldResult : Func :=
  { borrowed with
    results := [.ref .mutable (.int .i64)]
    roots := { results := #[[.param 0]] }
    blocks := #[⟨[(0, .data (.ref .readOnly recordTy))], [
      .def 1 (.fieldAddr 0 1), .term (.ret [1] none)]⟩] }

#guard rejected (withExtra fieldResult) .v030
#guard rejected (withExtra { borrowed with
  slots := #[⟨.ref .mutable (.int .i64), .immutable, 0, 0⟩]
  scopes := #[none]
  blocks := #[⟨[(0, .data (.ref .readOnly recordTy))], [
    .eff (.enter 0), .def 1 (.fieldAddr 0 1), .eff (.slotInit 0 1 (some 0)),
    .eff (.leave 0), .term (.ret [] none)]⟩] }) .v030

private def aggregateBorrow : Module :=
  let callee : Func :=
    { borrowed with
      params := [.ref .mutable recordTy]
      roots := { params := #[(0, [.param 0])] }
      blocks := #[⟨[(0, .data (.ref .mutable recordTy))], [.term (.ret [] none)]⟩] }
  let caller := { nested with blocks := #[⟨[], [
    .eff (.enter 0), .def 0 (.constInt .u8 1), .def 1 (.constInt .i64 42),
    .def 2 (.structLit recordTy [0, 1]), .def 3 (.structLit nestedTy [2]),
    .eff (.slotInit 0 3 (some 0)), .def 4 (.slotAddr 0), .def 5 (.fieldAddr 4 0),
    .def 6 (.call 2 [5] (some 0)), .eff (.leave 0), .term (.ret [] none)]⟩] }
  { mod with
    structs := #[descriptor, { byteSize := 9, fields := #[⟨recordTy, .mutable, .readOnly, 0⟩] }]
    funcs := #[fn, caller, callee] }

#guard rejected aggregateBorrow .v030

private def ownerArrayCore (slice : Bool) : Core.Module :=
  match core.impls[0]? with
  | none => core
  | some impl =>
    let arr := Ty.arr (.int .i64) 2
    let elem := Place.elem (if slice then .val (.read (.var 1)) else .of (.var 0)) (.lit .i64 1) 0
    { core with
      profile := .pilot
      types := #[arr]
      structs := #[]
      impls := #[{ impl with
        vars := #[⟨"a", arr, .immutable, 0, 0⟩] ++
          (if slice then #[⟨"s", .slice .mutable (.int .i64), .immutable, 0, 0⟩] else #[])
        body := .mk 0 ([.letS 0 (.arrLit arr [.lit .i64 1, .lit .i64 2]) 0] ++
          (if slice then [.letS 1 (.slice .mutable (.of (.var 0)) .omitted .omitted 0) 0] else []) ++
          [.assign elem (.lit .i64 9) 0, .print [.expr (.read elem)] 0]) none }] }

#guard accepted (Goose.Lower.lower (ownerArrayCore false))
#guard ran (Goose.Lower.lower (ownerArrayCore false)) "9\n"
#guard accepted (Goose.Lower.lower (ownerArrayCore true))
#guard ran (Goose.Lower.lower (ownerArrayCore true)) "9\n"

end Goose.GIR.StructChecks
