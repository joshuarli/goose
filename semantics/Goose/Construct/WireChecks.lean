import Goose.Construct.Writer

namespace Goose.Construct.WireChecks
open Goose.Core (NonlocalTarget)

private def module : Module := {
  files := #["construction.goose"]
  types := #[.int .u8, .varr (.int .u8), .varr (.varr (.int .u8))]
  globals := #[]
  impls := #[{
    name := "builder"
    params := #[]
    results := #[⟨.varr (.int .u8), .value, some 0⟩]
    vars := #[⟨"result", .varr (.int .u8), .mutable, 0, 0⟩,
      ⟨"second", .varr (.int .u8), .mutable, 0, 0⟩]
    body := .mk 0 [
      .letS 0 (.bytes (.varr (.int .u8)) [0, 255] 0) 0,
      .expr (.str (.varr (.int .u8)) [.text "hello", .view (.of (.var 0))] 0) 0,
      .expr (.copy (.varr (.int .u8)) (.var 0) 0) 0,
      .receive [0, 1] (.values [.resultLocal 0 0, .bytes (.varr (.int .u8)) [] 0]) 0,
      .appendValue (.var 0) (.arrLit (.arr (.int .u8) 1) [.lit .u8 1]) 0,
      .appendConstruct (.var 0) (.bytes (.varr (.int .u8)) [1] 0) 0,
      .retForward (.call 0 [.construct (.bytes (.varr (.int .u8)) [] 0)] 0) 0,
      .returnFromForward 0 (.call 0 [] 0) 0,
      .breakValue (.bytes (.varr (.int .u8)) [] 0) 0,
      .returnFrom 0 [.resultLocal 0 0] 0,
      .retValues [.resultLocal 0 0] 0] none
    summary := .known ⟨[], [], [], [], [], [0], [0], [0], false, true⟩ }]
  contexts := #[⟨0, "builder", [], [[]], []⟩]
  entry := 0
  origins := #[⟨0, 1, "return"⟩]
  structs := #[]
  targets := #[⟨0, []⟩] }

private def roundTrips (input : Module) : Bool :=
  match Decode.decodeBytes (Writer.module input).toUTF8 with
  | .ok decoded => Writer.module decoded == Writer.module input
  | .error _ => false

private def rejects (input : String) : Bool :=
  match Decode.decodeBytes input.toUTF8 with
  | .ok _ => false
  | .error _ => true

private def validModule : Module :=
  { module with
    types := module.types.push (.arr (.int .u8) 1) }

#guard roundTrips validModule
#guard rejects ((Writer.module validModule).replace "[0,255]" "[0,256]")
#guard rejects ((Writer.module validModule).replace "[\"target\",[0]]" "[\"target\",[]]")
#guard rejects ((Writer.module validModule).replace "[\"target\",[0]]" "[\"target\",[0,0]]")
#guard rejects ((Writer.module validModule).replace "[\"target\",[0]]" "[\"target\",[1]]")
#guard rejects ((Writer.module validModule).replace "\"value\"" "\"values\"")
#guard rejects ((Writer.module validModule).replace "core-construction" "core-shrink")
#guard rejects ((Writer.module validModule).replace "core-construction" "core-pilot")
#guard match Goose.Core.Decode.decodeBytes (Writer.module validModule).toUTF8 with
  | .ok _ => false
  | .error _ => true

#guard (.varr (.varr (.int .u8)) : Ty).constructible
#guard (.arr (.varr (.int .u8)) 2 : Ty).nonfixed
#guard !(Ty.growshrink (.varr (.int .u8))).constructible
#guard !(Ty.limited (.varr (.int .u8)) 4).constructible


private def namedStructModule : Module := { validModule with
  types := validModule.types.push (.structT 0 (.cons (.int .u8) .nil))
  structs := #[⟨1,#[⟨.int .u8,.immutable,.mutable,0⟩],"箱"⟩] }
#guard roundTrips namedStructModule
#guard rejects ((Writer.module namedStructModule).replace ",\"箱\"]" "]")
#guard rejects ((Writer.module namedStructModule).replace "\"箱\"" "\"\"")
#guard rejects ((Writer.module namedStructModule).replace ",\"箱\"]" ",\"箱\",\"extra\"]")

end Goose.Construct.WireChecks
