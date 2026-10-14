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

namespace Goose.Construct.GIR.Checks

private def known (constructs needs escapes : List Nat := []) (aborts outputs : Bool := false) : SummaryAnn :=
  .known ⟨[],[],[],[],[],constructs,needs,escapes,aborts,outputs⟩

private def targeted : Module :=
  let entry := function "entry" #[⟨[],[
    .eff (.enter 0), .def 0 (.destOpen (.slot 0) byteTy .value none (some 0)),
    .def 1 (.callConstruct 1 [] [0] (some 0)), .eff (.destPublish 1 (some 0)),
    .def 2 (.slotAddr 0), .def 3 (.snapshot .owner 2), .eff (.print [.val 3] (some 0)),
    .eff (.leave 0), .term (.ret [] (some 0))]⟩] #[⟨byteTy,.mutable,0,0⟩]
  let producer := function "producer" #[
    ⟨[(0,.dest byteTy .value)],[.term (.invoke 2 [] [] 1 [0] [⟨0,2,[0]⟩] (some 0))]⟩,
    ⟨[(1,.dest byteTy .value)],[.def 2 (.destAbandon 1 (some 0)),
      .eff (.destCancel 2 (some 0)), .term (.abort .userAbort (some 0))]⟩,
    ⟨[(3,.built byteTy .value),(4,.dest byteTy .value)],[
      .def 5 (.destAbandon 4 (some 0)), .eff (.destCancel 5 (some 0)),
      .def 6 (.destRelocate 3 .exitValue (some 0)), .term (.ret [6] (some 0))]⟩]
      #[] [⟨byteTy,.value,none⟩]
  let helper := function "helper" #[⟨[],[
    .def 0 (.targetDest 0 0 (some 0)), .eff (.destBytes 0 [65,0,255] (some 0)),
    .def 1 (.destFinish 0 (some 0)), .term (.escape 0 [1] [] (some 0))]⟩]
  { (moduleOf #[{ entry with summary := known [] [] [] true true },
      { producer with summary := known [0] [] [] true false },
      { helper with summary := known [] [0] [0] false false }]) with targets := #[⟨1,[]⟩] }

#guard (Validate.validate targeted).isOk
#guard observation targeted == some ([65,0,255,10],
  [.begin 0,.begin 1,.write 1 0,.write 1 1,.write 1 2,.abandon 0,.relocate 1 .exitValue,.publish 1])
#guard roundTrip targeted

private def namedResult : Module :=
  let entry := multiple.funcs[0]
  let entry := { entry with blocks := #[⟨[],[
    .eff (.enter 0), .def 0 (.destOpen (.slot 0) byteTy .value none (some 0)),
    .def 1 (.callConstruct 1 [] [0] (some 0)), .eff (.destPublish 1 (some 0)),
    .def 2 (.slotAddr 0), .def 3 (.snapshot .owner 2), .eff (.print [.val 3] (some 0)),
    .eff (.leave 0), .term (.ret [] (some 0))]⟩] }
  let producer := function "named" #[⟨[(0,.dest byteTy .value)],[
    .eff (.enter 0), .eff (.destBytes 0 [65] (some 0)), .def 1 (.destFinish 0 (some 0)),
    .eff (.destBind 0 1 (some 0)), .def 2 (.destNamed 0 (some 0)),
    .eff (.leave 0), .term (.ret [2] (some 0))]⟩] #[⟨byteTy,.mutable,0,0⟩]
    [⟨byteTy,.value,some 0⟩]
  moduleOf #[entry,producer]

#guard (Validate.validate namedResult).isOk
#guard observation namedResult == some ([65,10],[.begin 0,.write 0 0,.publish 0])
#guard roundTrip namedResult

private def alternateNamed : Module :=
  let producer := namedResult.funcs[1]
  let producer := { producer with blocks := #[⟨[(0,.dest byteTy .value)],[
    .eff (.enter 0), .eff (.destBytes 0 [65] (some 0)), .def 1 (.destFinish 0 (some 0)),
    .eff (.destBind 0 1 (some 0)), .def 2 (.resultExitDest 0 (some 0)),
    .eff (.destBytes 2 [66,67] (some 0)), .def 3 (.destFinish 2 (some 0)),
    .def 4 (.destAbandonNamed 0 3 (some 0)), .eff (.destCancel 4 (some 0)),
    .def 5 (.destRelocate 3 .exitValue (some 0)), .eff (.leave 0), .term (.ret [5] (some 0))]⟩] }
  { namedResult with funcs := #[namedResult.funcs[0],producer] }

#guard (Validate.validate alternateNamed).isOk
#guard observation alternateNamed == some ([66,67,10],
  [.begin 0,.write 0 0,.begin 1,.write 1 0,.write 1 1,.abandon 0,.relocate 1 .exitValue,.publish 1])
#guard roundTrip alternateNamed

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def nominal : Module :=
  let ty := Ty.structT 0 (TyList.ofList [.int .u8,.int .i64])
  let array := Ty.varr ty
  { (moduleOf #[function "entry" #[⟨[],[
      .eff (.enter 0), .def 0 (.constInt .u8 65), .def 1 (.constInt .i64 7),
      .def 2 (.structLit ty [0,1]), .eff (.slotInit 0 2 (some 0)),
      .def 3 (.destOpen (.slot 1) array .value none (some 0)), .eff (.destWrite 3 2 (some 0)),
      .def 4 (.destFinish 3 (some 0)), .eff (.destPublish 4 (some 0)),
      .def 5 (.slotAddr 1), .def 6 (.snapshot .owner 5), .eff (.print [.val 6] (some 0)),
      .eff (.leave 0), .term (.ret [] (some 0))]⟩] #[⟨ty,.mutable,0,0⟩,⟨array,.mutable,0,1⟩]])
    with structs := #[⟨16,#[⟨.int .u8,.mutable,.mutable,0⟩,⟨.int .i64,.mutable,.mutable,8⟩],"箱"⟩] }

#guard (Validate.validate nominal).isOk
#guard observation nominal == some (("[箱 { 65, 7 }]\n".toUTF8.data.toList),[.begin 0,.write 0 0,.publish 0])
#guard roundTrip nominal
#guard !(Decode.decodeBytes ((Writer.write nominal).replace ",\"箱\"]" "]").toUTF8).isOk
#guard !(Decode.decodeBytes ((Writer.write nominal).replace ",\"箱\"]" ",\"\"]").toUTF8).isOk

private def globalBytes : Module :=
  let init := function "init" #[⟨[(0,.dest byteTy .value)],[.eff (.destBytes 0 [65,0,255] (some 0)),
    .def 1 (.destFinish 0 (some 0)), .term (.ret [1] (some 0))]⟩] #[] [⟨byteTy,.value,none⟩]
  { (moduleOf #[function "entry" #[⟨[],[.def 0 (.globalAddr 0), .def 1 (.snapshot .owner 0),
      .eff (.print [.val 1] (some 0)), .term (.ret [] (some 0))]⟩]]) with
    globals := #[⟨"bytes",byteTy,.immutable,init,0⟩] }

#guard (Validate.validate globalBytes).isOk
#guard observation globalBytes == some ([65,0,255,10],[.begin 0,.write 0 0,.write 0 1,.write 0 2,.publish 0])
#guard roundTrip globalBytes

private def wrongResultReceiver : Module :=
  let producer := namedResult.funcs[1]
  let producer := { producer with blocks := #[⟨[(0,.dest byteTy .value)],[
    .eff (.enter 0), .def 1 (.destOpen (.slot 0) byteTy .value none (some 0)),
    .eff (.destBytes 1 [65] (some 0)), .def 2 (.destFinish 1 (some 0)),
    .def 3 (.destAbandon 0 (some 0)), .eff (.destCancel 3 (some 0)),
    .eff (.leave 0), .term (.ret [2] (some 0))]⟩], results := [⟨byteTy,.value,none⟩] }
  { namedResult with funcs := #[namedResult.funcs[0],producer] }

#guard (match Validate.validate wrongResultReceiver with | .error v => v.code == .v060 | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def ownedArgument : Module :=
  let entry := function "entry" #[⟨[],[
    .def 0 (.destOpen (.arg 1 0) byteTy .value none (some 0)), .eff (.destBytes 0 [65,255] (some 0)),
    .def 1 (.destFinish 0 (some 0)), .def 2 (.destArg 1 (some 0)),
    .def 3 (.call 1 [2] (some 0)), .term (.ret [] (some 0))]⟩]
  let callee := function "owned" #[⟨[(0,.data (.ref .mutable byteTy))],[
    .eff (.enter 0), .eff (.slotInit 0 0 (some 0)), .def 1 (.slotAddr 0),
    .def 2 (.snapshot .owner 1), .eff (.print [.val 2] (some 0)), .eff (.leave 0), .term (.ret [] (some 0))]⟩]
    #[⟨byteTy,.immutable,0,0⟩]
  moduleOf #[entry,{ callee with params := [byteTy] }]

#guard (Validate.validate ownedArgument).isOk
#guard observation ownedArgument == some ([65,255,10],[.begin 0,.write 0 0,.write 0 1,.publish 0])
#guard roundTrip ownedArgument

private def wrongArgumentCallee : Module :=
  let entry := ownedArgument.funcs[0]
  let block := entry.blocks[0]
  { ownedArgument with funcs := #[{ entry with blocks := #[{ block with insts := block.insts.take 4 ++
    [.def 3 (.call 0 [2] (some 0)),.term (.ret [] (some 0))] }] },ownedArgument.funcs[1]] }

#guard !(Validate.validate wrongArgumentCallee).isOk

private def fittingKnown : Module :=
  let original := staged 2
  { original with funcs := original.funcs.map fun f => { f with summary := known [] [] [] false true } }

#guard (Validate.validate fittingKnown).isOk
#guard roundTrip fittingKnown

private def omittedOverflow : Module :=
  let original := staged 1
  { original with funcs := original.funcs.map fun f => { f with summary := known [] [] [] false true } }

#guard (match Validate.validate omittedOverflow with | .error v => v.code == .v050 | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def growthDuringAppend : Module :=
  let ty := Ty.grow (.int .u8)
  moduleOf #[function "entry" #[⟨[],[
    .eff (.enter 0), .def 0 (.destOpen (.slot 0) ty .value none (some 0)),
    .eff (.destBytes 0 [] (some 0)), .def 1 (.destFinish 0 (some 0)), .eff (.destPublish 1 (some 0)),
    .def 2 (.slotAddr 0), .def 3 (.destOpen (.append 2) byteTy .elementRun none (some 0)),
    .def 4 (.constInt .u8 65), .def 5 (.push 2 4 (some 0)),
    .eff (.destBytes 3 [66] (some 0)), .def 6 (.destFinish 3 (some 0)),
    .eff (.destPublish 6 (some 0)), .eff (.leave 0), .term (.ret [] (some 0))]⟩]
    #[⟨ty,.mutable,0,0⟩]]

#guard (match Validate.validate growthDuringAppend with | .error v => v.code == .v060 | _ => false)

private def missingOrigin : Module :=
  let entry := rawBytes.funcs[0]
  let block := entry.blocks[0]
  { rawBytes with funcs := #[{ entry with blocks := #[{ block with insts := (block.insts.take 2 ++
      [.eff (.destBytes 0 [65,0,255] none)] ++ block.insts.drop 3) }] }] }

#guard (match Validate.validate missingOrigin with | .error v => v.code == .v100 | _ => false)

private def escapedOwnedReference : Module :=
  let entry := ownedArgument.funcs[0]
  let callee := ownedArgument.funcs[1]
  let callee := { callee with
    results := [⟨.ref .readOnly byteTy,.register,none⟩]
    roots := { results := #[[.param 0]] }
    blocks := #[⟨[(0,.data (.ref .mutable byteTy))],[
      .eff (.enter 0), .eff (.slotInit 0 0 (some 0)), .def 1 (.slotAddr 0),
      .eff (.leave 0), .term (.ret [1] (some 0))]⟩] }
  moduleOf #[entry,callee]

#guard (match Validate.validate escapedOwnedReference with | .error v => v.code == .v040 | _ => false)

end Goose.Construct.GIR.Checks
