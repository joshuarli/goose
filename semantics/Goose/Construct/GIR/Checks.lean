import Goose.Construct.GIR.Run
import Goose.Construct.GIR.Json

namespace Goose.Construct.GIR.Checks

private def byteTy : Ty := .varr (.int .u8)

private def function (name : String) (blocks : Array Block) (slots : Array Slot := #[])
    (results : List ResultDescriptor := []) : Func :=
  ⟨name, [], results, slots, #[none], blocks, { results := results.map (fun _ => []) |>.toArray }, .unknown, some 0, none⟩

private def moduleOf (functions : Array Func) : Module :=
  { files := #["gir.goose"], globals := #[], funcs := functions, entry := 0,
    origins := #[⟨0,17,"print"⟩], structs := #[], targets := #[], types := #[] }

private def rawBytes : Module := moduleOf #[function "entry" #[⟨[],[
  .eff (.enter 0),
  .def 0 (.destOpen (.slot 0) byteTy .value none (some 0)),
  .eff (.destBytes 0 [65,0,255] (some 0)),
  .def 1 (.destFinish 0 (some 0)),
  .eff (.destPublish 1 (some 0)),
  .def 2 (.slotAddr 0), .def 3 (.snapshot .owner 2),
  .eff (.print [.val 3] (some 0)), .eff (.leave 0), .term (.ret [] (some 0))]⟩]
  #[⟨byteTy,.mutable,0,0⟩]]

private def observation (module : Module) : Option (List UInt8 × List Core.ConstructionEvent) :=
  match Run.run 1000 .release module with
  | .done .returned stdout events => some (stdout.data.toList,events)
  | _ => none

#guard (Validate.validate rawBytes).isOk
#guard observation rawBytes == some ([65,0,255,10],[.begin 0,.write 0 0,.write 0 1,.write 0 2,.publish 0])
#guard (match Run.run 0 .release rawBytes with | .timeout stdout events => stdout.isEmpty && events.isEmpty | _ => false)

private def duplicatePublish : Module :=
  let entry := rawBytes.funcs[0]
  let block := entry.blocks[0]
  { rawBytes with funcs := #[{ entry with blocks := #[{ block with insts := block.insts.take 5 ++ [.eff (.destPublish 1 (some 0))] ++ block.insts.drop 5 }] }] }

#guard (match Validate.validate duplicatePublish with | .error error => error.code == .v060 | _ => false)

private def wrongType : Module :=
  let entry := rawBytes.funcs[0]
  let block := entry.blocks[0]
  { rawBytes with funcs := #[{ entry with blocks := #[{ block with insts := block.insts.take 2 ++ [.eff (.destWrite 0 2 (some 0))] ++ block.insts.drop 2 }] }] }

#guard (match Validate.validate wrongType with | .error error => error.code == .v010 | _ => false)

private def multiple : Module := moduleOf #[
  function "entry" #[⟨[],[
    .eff (.enter 0), .def 0 (.destOpen (.slot 0) byteTy .value none (some 0)),
    .def 1 (.callConstruct 1 [] [0] (some 0)), .def 2 (.result 1 0), .def 3 (.result 1 1),
    .eff (.destPublish 3 (some 0)), .def 4 (.slotAddr 0), .def 5 (.snapshot .owner 4),
    .eff (.print [.val 2,.val 5] (some 0)), .eff (.leave 0), .term (.ret [] (some 0))]⟩] #[⟨byteTy,.mutable,0,0⟩],
  function "producer" #[⟨[(0,.dest byteTy .value)],[
    .def 1 (.constInt .i64 7), .eff (.destBytes 0 [65] (some 0)),
    .def 2 (.destFinish 0 (some 0)), .term (.ret [1,2] (some 0))]⟩]
    #[] [⟨.int .i64,.register,none⟩,⟨byteTy,.value,none⟩]]

#guard (Validate.validate multiple).isOk
#guard observation multiple == some ([55,65,10],[.begin 0,.write 0 0,.publish 0])

private def nested : Module := moduleOf #[function "entry" #[⟨[],[
  .eff (.enter 0), .def 0 (.destOpen (.slot 0) (.varr byteTy) .value none (some 0)),
  .def 1 (.destChild 0 byteTy (some 0)), .eff (.destBytes 1 [65,0] (some 0)),
  .def 2 (.destFinish 1 (some 0)), .eff (.destAttach 0 2 (some 0)),
  .def 3 (.destChild 0 byteTy (some 0)), .eff (.destBytes 3 [255] (some 0)),
  .def 4 (.destFinish 3 (some 0)), .eff (.destAttach 0 4 (some 0)),
  .def 5 (.destFinish 0 (some 0)), .eff (.destPublish 5 (some 0)),
  .def 6 (.slotAddr 0), .def 7 (.snapshot .owner 6),
  .eff (.print [.val 7] (some 0)), .eff (.leave 0), .term (.ret [] (some 0))]⟩]
  #[⟨.varr byteTy,.mutable,0,0⟩]]

#guard (Validate.validate nested).isOk
#guard observation nested == some ([91,34,65,0,34,44,32,34,255,34,93,10],
  [.begin 0,.begin 1,.write 1 0,.write 1 1,.write 0 0,.begin 2,.write 2 0,.write 0 1,.publish 0])

private def roundTrip (module : Module) : Bool :=
  match Decode.decodeBytes (Writer.write module).toUTF8 with
  | .error _ => false
  | .ok decoded => (Validate.validate decoded).isOk && observation decoded == observation module

#guard roundTrip rawBytes
#guard roundTrip multiple
#guard roundTrip nested

private def malformedBytes : String := "[\"module\",\"gir-h/0.4\",\"core-construction\",[],[],[],[],[],[],0]"
#guard !(Decode.decodeBytes malformedBytes.toUTF8).isOk

private def malformedByteValue : Bool :=
  let bytes := (Writer.write rawBytes).replace "[65,0,255]" "[65,0,256]"
  !(Decode.decodeBytes bytes.toUTF8).isOk

#guard malformedByteValue

private def staged (capacity : Nat) : Module :=
  let ty := Ty.limited (.int .u8) capacity
  moduleOf #[function "entry" #[⟨[],[
    .eff (.enter 0), .def 0 (.destOpen (.slot 0) ty .value none (some 0)),
    .def 1 (.destStage 0 (some 0)), .eff (.destBytes 1 [65,66] (some 0)),
    .def 2 (.destFinish 1 (some 0)), .def 3 (.destFit 2 (some 0)),
    .eff (.destPublish 3 (some 0)), .def 4 (.slotAddr 0), .def 5 (.snapshot .owner 4),
    .eff (.print [.val 5] (some 0)), .eff (.leave 0), .term (.ret [] (some 0))]⟩]
    #[⟨ty,.mutable,0,0⟩]]

#guard (Validate.validate (staged 2)).isOk
#guard observation (staged 2) == some ([65,66,10],
  [.begin 0,.stage 0,.write 0 0,.write 0 1,.copy (.storage 1 []) 0,.publish 0])
#guard roundTrip (staged 2)
#guard (match Run.run 1000 .release (staged 1) with
  | .done (.aborted .capacity 0) stdout events => stdout.isEmpty &&
      events == [.begin 0,.stage 0,.write 0 0,.write 0 1]
  | _ => false)

end Goose.Construct.GIR.Checks
