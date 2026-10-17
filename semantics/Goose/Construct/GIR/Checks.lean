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
  [.begin 0,.write 0 0,.write 0 1,.write 0 2,.publish 0])
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

private def ordinaryOpenResultExit : Module :=
  let entry := namedResult.funcs[0]
  let producer := function "ordinary" #[⟨[(0,.dest byteTy .value)],[
    .eff (.enter 0), .def 1 (.resultExitDest 0 (some 0)), .eff (.destBytes 1 [65,66] (some 0)),
    .def 2 (.destFinish 1 (some 0)), .def 3 (.destAbandon 0 (some 0)),
    .eff (.destCancel 3 (some 0)), .def 4 (.destRelocate 2 .exitValue (some 0)),
    .eff (.leave 0), .term (.ret [4] (some 0))]⟩]
    #[] [⟨byteTy,.value,none⟩]
  { namedResult with funcs := #[entry,producer] }

#guard (Validate.validate ordinaryOpenResultExit).isOk
#guard observation ordinaryOpenResultExit == some ([65,66,10],
  [.begin 0,.write 0 0,.write 0 1,.publish 0])
#guard roundTrip ordinaryOpenResultExit

private def ordinaryPartialResultExit : Module :=
  let entry := ordinaryOpenResultExit.funcs[0]
  let producer := function "ordinaryPartial" #[⟨[(0,.dest byteTy .value)],[
    .eff (.enter 0), .eff (.destBytes 0 [65] (some 0)), .def 1 (.resultExitDest 0 (some 0)),
    .eff (.destBytes 1 [66] (some 0)), .def 2 (.destFinish 1 (some 0)),
    .def 3 (.destAbandon 0 (some 0)), .eff (.destCancel 3 (some 0)),
    .def 4 (.destRelocate 2 .exitValue (some 0)), .eff (.leave 0), .term (.ret [4] (some 0))]⟩]
    #[] [⟨byteTy,.value,none⟩]
  { ordinaryOpenResultExit with funcs := #[entry,producer] }

#guard (Validate.validate ordinaryPartialResultExit).isOk
#guard observation ordinaryPartialResultExit == some ([66,10],
  [.begin 0,.write 0 0,.begin 1,.write 1 0,.abandon 0,.relocate 1 .exitValue,.publish 1])
#guard roundTrip ordinaryPartialResultExit

private def ordinaryOpenResultExitCapacityFault : Module :=
  let limitedByte := Ty.limited (.int .u8) 1
  let entry := function "entry" #[⟨[],[
    .eff (.enter 0), .def 0 (.destOpen (.slot 0) limitedByte .value none (some 0)),
    .def 1 (.callConstruct 1 [] [0] (some 0)), .eff (.destPublish 1 (some 0)),
    .eff (.leave 0), .term (.ret [] (some 0))]⟩] #[⟨limitedByte,.mutable,0,0⟩]
  let producer := function "ordinaryCapacity" #[⟨[(0,.dest limitedByte .value)],[
    .eff (.enter 0), .def 1 (.resultExitDest 0 (some 0)),
    .eff (.destBytes 1 [65,66] (some 0)), .def 2 (.destFinish 1 (some 0)),
    .def 3 (.destAbandon 0 (some 0)), .eff (.destCancel 3 (some 0)),
    .def 4 (.destRelocate 2 .exitValue (some 0)), .eff (.leave 0),
    .term (.ret [4] (some 0))]⟩] #[] [⟨limitedByte,.value,none⟩]
  { ordinaryOpenResultExit with funcs := #[entry,producer] }

#guard (Validate.validate ordinaryOpenResultExitCapacityFault).isOk
#guard (match Run.run 1000 .release ordinaryOpenResultExitCapacityFault with
  | .done (.aborted .capacity 0) stdout events => stdout.isEmpty && events == [.begin 0,.write 0 0]
  | _ => false)
#guard roundTrip ordinaryOpenResultExitCapacityFault

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

namespace Goose.Construct.GIR.Checks

private def pushedNested : Module :=
  let ty := Ty.grow byteTy
  moduleOf #[function "entry" #[⟨[],[
    .eff (.enter 0), .def 6 (.constInt .i64 7), .eff (.slotInit 0 6 (some 0)),
    .def 0 (.destOpen (.slot 1) ty .value none (some 0)),
    .def 1 (.destFinish 0 (some 0)), .eff (.destPublish 1 (some 0)), .def 2 (.slotAddr 1),
    .def 3 (.destOpen (.push 2) byteTy .value none (some 0)), .eff (.destBytes 3 [65,0,255] (some 0)),
    .def 4 (.destFinish 3 (some 0)), .eff (.destPublish 4 (some 0)),
    .def 5 (.snapshot .owner 2), .eff (.print [.val 5] (some 0)),
    .eff (.leave 0), .term (.ret [] (some 0))]⟩] #[⟨.int .i64,.mutable,0,0⟩,⟨ty,.mutable,0,1⟩]]

#guard (Validate.validate pushedNested).isOk
#guard observation pushedNested == some (("[\"A".toUTF8 ++ ⟨#[0,255]⟩ ++ "\"]\n".toUTF8).data.toList,
  [.begin 0,.publish 0,.begin 1,.write 1 0,.write 1 1,.write 1 2,.publish 1])
#guard roundTrip pushedNested

private def branchWire : String := "[\"module\",\"gir-h/0.4\",\"core-construction\",[[\"file\",\"sem_construction_bytes.goose\"]],[[\"int\",\"u8\"],[\"grow\",0],[\"int\",\"i64\"],[\"dest\",1,\"value\"],[\"built\",1,\"value\"]],[],[],[],[[\"func\",\"main\",[],[],[[\"slot\",1,\"let\",0,0],[\"slot\",2,\"let\",0,1],[\"slot\",1,\"let\",0,2],[\"slot\",1,\"let\",0,3]],[[\"scope\",[]],[\"scope\",[0]],[\"scope\",[0]],[\"scope\",[0]],[\"scope\",[0]],[\"scope\",[0]]],[[\"block\",[],[[\"x_enter\",0],[\"i_int\",0,2,\"3\"],[\"i_dest_open\",1,[\"dr_slot\",0],1,\"value\",[0],[4]],[\"x_dest_bytes\",1,[65,0,66],[4]],[\"i_dest_finish\",2,1,[4]],[\"x_dest_publish\",2,[4]],[\"i_slot\",3,0],[\"i_snap\",4,\"owner\",3],[\"i_vlen\",5,4],[\"i_int\",6,2,\"3\"],[\"i_cmp\",7,\"eq\",2,5,6],[\"t_condbr\",7,1,[],2,[]]]],[\"block\",[],[[\"x_enter\",1],[\"i_int\",8,2,\"1\"],[\"x_leave\",1],[\"t_br\",3,[8]]]],[\"block\",[],[[\"x_enter\",2],[\"i_int\",9,2,\"2\"],[\"x_leave\",2],[\"t_br\",3,[9]]]],[\"block\",[[\"bp\",10,2]],[[\"x_init\",1,10,[1]],[\"i_slot\",11,0],[\"i_snap\",12,\"owner\",11],[\"i_vlen\",13,12],[\"i_int\",14,2,\"3\"],[\"i_cmp\",15,\"eq\",2,13,14],[\"t_condbr\",15,4,[],5,[]]]],[\"block\",[],[[\"x_enter\",3],[\"i_int\",16,2,\"3\"],[\"i_dest_open\",17,[\"dr_slot\",2],1,\"value\",[16],[5]],[\"x_dest_bytes\",17,[67,0,68],[5]],[\"i_dest_finish\",18,17,[5]],[\"x_dest_publish\",18,[5]],[\"x_leave\",3],[\"t_br\",6,[]]]],[\"block\",[],[[\"x_enter\",4],[\"i_int\",19,2,\"1\"],[\"i_dest_open\",20,[\"dr_slot\",2],1,\"value\",[19],[6]],[\"x_dest_bytes\",20,[69],[6]],[\"i_dest_finish\",21,20,[6]],[\"x_dest_publish\",21,[6]],[\"x_leave\",4],[\"t_br\",6,[]]]],[\"block\",[],[[\"x_enter\",5],[\"i_int\",22,2,\"3\"],[\"i_dest_open\",23,[\"dr_slot\",3],1,\"value\",[22],[7]],[\"x_dest_bytes\",23,[70,0,71],[7]],[\"i_dest_finish\",24,23,[7]],[\"x_dest_publish\",24,[7]],[\"x_leave\",5],[\"i_slot\",25,1],[\"i_load\",26,25],[\"x_print\",[[\"pp_val\",26]],[8]],[\"i_slot\",27,0],[\"i_snap\",28,\"owner\",27],[\"i_vlen\",29,28],[\"i_slot\",30,0],[\"i_snap\",31,\"owner\",30],[\"i_int\",32,2,\"0\"],[\"i_index\",33,31,32,[9]],[\"i_load\",34,33],[\"i_slot\",35,0],[\"i_snap\",36,\"owner\",35],[\"i_int\",37,2,\"2\"],[\"i_index\",38,36,37,[9]],[\"i_load\",39,38],[\"x_print\",[[\"pp_val\",29],[\"pp_text\",\" \"],[\"pp_val\",34],[\"pp_text\",\" \"],[\"pp_val\",39]],[10]],[\"i_slot\",40,2],[\"i_snap\",41,\"owner\",40],[\"i_vlen\",42,41],[\"i_slot\",43,2],[\"i_snap\",44,\"owner\",43],[\"i_int\",45,2,\"2\"],[\"i_index\",46,44,45,[11]],[\"i_load\",47,46],[\"x_print\",[[\"pp_val\",42],[\"pp_text\",\" \"],[\"pp_val\",47]],[12]],[\"i_slot\",48,3],[\"i_snap\",49,\"owner\",48],[\"i_vlen\",50,49],[\"i_slot\",51,3],[\"i_snap\",52,\"owner\",51],[\"i_int\",53,2,\"1\"],[\"i_index\",54,52,53,[13]],[\"i_load\",55,54],[\"x_print\",[[\"pp_val\",50],[\"pp_text\",\" \"],[\"pp_val\",55]],[14]],[\"x_leave\",0],[\"t_ret\",[],[]]]]],[\"roots\",[],[],[]],[\"summary\",[],[],[],[],[],[],[],[],1,1],[0],[]]],0,[[\"origin\",0,2,\"let\"],[\"origin\",0,3,\"let\"],[\"origin\",0,8,\"let\"],[\"origin\",0,13,\"let\"],[\"origin\",0,2,\"expr\"],[\"origin\",0,9,\"expr\"],[\"origin\",0,11,\"expr\"],[\"origin\",0,14,\"expr\"],[\"origin\",0,16,\"print\"],[\"origin\",0,17,\"index\"],[\"origin\",0,17,\"print\"],[\"origin\",0,18,\"index\"],[\"origin\",0,18,\"print\"],[\"origin\",0,19,\"index\"],[\"origin\",0,19,\"print\"]]]"

private def branchObservation : Bool :=
  match Decode.decodeBytes branchWire.toUTF8 with
  | .error _ => false
  | .ok module => (Validate.validate module).isOk && observation module ==
      some ("1\n3 65 66\n3 68\n3 0\n".toUTF8.data.toList,
        [.begin 0,.write 0 0,.write 0 1,.write 0 2,.publish 0,
         .begin 1,.write 1 0,.write 1 1,.write 1 2,.publish 1,
         .begin 2,.write 2 0,.write 2 1,.write 2 2,.publish 2])

#guard branchObservation
#guard (match Decode.decodeBytes (branchWire.replace "\"i_int\",0,2,\"3\"" "\"i_int\",0,2,\"0\"").toUTF8 with
  | .ok module => match Validate.validate module with | .error v => v.code == .v060 | _ => false
  | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def recursiveTarget : Module :=
  let entry := function "entry" #[⟨[],[
    .eff (.enter 0), .def 0 (.destOpen (.slot 0) byteTy .value none (some 0)), .def 1 (.constInt .i64 1),
    .def 2 (.callConstruct 1 [1] [0] (some 0)), .eff (.destPublish 2 (some 0)),
    .def 3 (.slotAddr 0), .def 4 (.snapshot .owner 3), .eff (.print [.val 4] (some 0)),
    .eff (.leave 0), .term (.ret [] none)]⟩] #[⟨byteTy,.mutable,0,0⟩]
  let recursive := function "recursive" #[
    ⟨[(0,.data (.int .i64)),(1,.dest byteTy .value)],[
      .eff (.enter 0), .eff (.slotInit 0 0 (some 0)), .def 2 (.constInt .i64 0), .def 3 (.cmp .eq .i64 0 2),
      .term (.condbr 3 1 [] 2 [])]⟩,
    ⟨[],[.term (.invoke 2 [] [] 3 [1] [⟨0,4,[1]⟩] (some 0))]⟩,
    ⟨[],[.def 4 (.constInt .i64 1), .def 5 (.bin .sub .i64 0 4 (some 0)),
      .def 6 (.destOpen (.slot 1) byteTy .value none (some 0)), .def 7 (.callConstruct 1 [5] [6] (some 0)),
      .eff (.destPublish 7 (some 0)), .def 8 (.slotAddr 1), .def 9 (.snapshot .owner 8),
      .eff (.print [.val 9] (some 0)), .eff (.destBytes 1 [79] (some 0)),
      .def 10 (.destFinish 1 (some 0)), .eff (.leave 0), .term (.ret [10] (some 0))]⟩,
    ⟨[(11,.dest byteTy .value)],[.def 12 (.destAbandon 11 (some 0)), .eff (.destCancel 12 (some 0)),
      .eff (.leave 0), .term (.abort .userAbort (some 0))]⟩,
    ⟨[(13,.built byteTy .value),(14,.dest byteTy .value)],[.def 15 (.destAbandon 14 (some 0)),
      .eff (.destCancel 15 (some 0)), .def 16 (.destRelocate 13 .exitValue (some 0)),
      .eff (.leave 0), .term (.ret [16] (some 0))]⟩]
    #[⟨.int .i64,.immutable,0,0⟩,⟨byteTy,.mutable,0,1⟩] [⟨byteTy,.value,none⟩]
  let helper := function "helper" #[⟨[],[.def 0 (.targetDest 0 0 (some 0)),
    .eff (.destBytes 0 [73] (some 0)), .def 1 (.destFinish 0 (some 0)),
    .term (.escape 0 [1] [] (some 0))]⟩]
  { (moduleOf #[{ entry with summary := known [] [] [] true true },
      { recursive with params := [.int .i64], summary := known [0] [] [] true true },
      { helper with summary := known [] [0] [0] false false }]) with targets := #[⟨1,[]⟩] }

#guard (Validate.validate recursiveTarget).isOk
#guard observation recursiveTarget == some ([73,10,79,10],
  [.begin 0,.begin 1,.write 1 0,.publish 1,.write 0 0,.publish 0])
#guard roundTrip recursiveTarget

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def retainedLimitedReference : Module :=
  let ty := Ty.limited (.int .u8) 3
  moduleOf #[function "entry" #[⟨[],[
    .eff (.enter 0), .def 0 (.constInt .i64 3), .def 1 (.destOpen (.slot 0) ty .value (some 0) (some 0)),
    .eff (.destBytes 1 [1,2,3] (some 0)), .def 2 (.destFinish 1 (some 0)), .eff (.destPublish 2 (some 0)),
    .def 3 (.slotAddr 0), .def 4 (.snapshot .owner 3), .def 5 (.constInt .i64 2),
    .def 6 (.indexChecked 4 5 (some 0)), .eff (.popN 3 5 (some 0)), .def 7 (.constInt .u8 7),
    .eff (.store 6 7 (some 0)), .def 8 (.load 6), .def 9 (.snapshot .owner 3), .def 10 (.viewLen 9),
    .eff (.print [.val 8,.text " ",.val 10] (some 0)), .eff (.leave 0), .term (.ret [] none)]⟩]
    #[⟨ty,.immutable,0,0⟩]]

#guard (Validate.validate retainedLimitedReference).isOk
#guard observation retainedLimitedReference == some ("7 1\n".toUTF8.data.toList,
  [.begin 0,.write 0 0,.write 0 1,.write 0 2,.publish 0])
#guard roundTrip retainedLimitedReference

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def sliceBacking (includeBacking : Bool) : Module :=
  let array := Ty.arr (.int .u8) 2
  let slice := Ty.slice .readOnly (.int .u8)
  let entry := function "entry" #[⟨[],[
    .eff (.enter 0), .def 0 (.globalAddr 0), .def 1 (.snapshot .owner 0),
    .def 2 (.viewSlice .readOnly 1 .omitted .omitted (some 0)), .eff (.slotInit 0 2 (some 0)),
    .def 3 (.slotAddr 0), .def 4 (.call 1 [3] (some 0)),
    .eff (.leave 0), .term (.ret [] none)]⟩] #[⟨slice,.immutable,0,0⟩]
  let callee := function "reader" #[⟨[(0,.data (.ref .readOnly slice))],[
    .eff (.enter 0),.eff (.slotInit 0 0 (some 0)),
    .def 1 (.load 0), .def 2 (.sliceView 1), .eff (.print [.val 2] (some 0)),
    .eff (.leave 0),.term (.ret [] none)]⟩] #[⟨.ref .readOnly slice,.immutable,0,0⟩]
  let init := function "backing" #[⟨[],[.def 0 (.constInt .u8 65), .def 1 (.constInt .u8 66),
    .def 2 (.arrLit array [0,1]), .term (.ret [2] none)]⟩] #[] [⟨array,.register,none⟩]
  { (moduleOf #[entry,{ callee with
      params := [.ref .readOnly slice]
      roots := { params := #[(0,[.param 0])], contents := #[(0,if includeBacking then [.global 0] else [])] } }]) with
    globals := #[⟨"backing",array,.immutable,init,0⟩] }

#guard (Validate.validate (sliceBacking true)).isOk
#guard observation (sliceBacking true) == some ([65,66,10],[])
#guard roundTrip (sliceBacking true)
#guard (match Validate.validate (sliceBacking false) with | .error v => v.code == .v050 | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def renderBeforeMutation : Module := moduleOf #[function "entry" #[⟨[],[
  .eff (.enter 0), .def 0 (.destOpen (.slot 0) byteTy .value none (some 0)),
  .eff (.destBytes 0 [65] (some 0)), .def 1 (.destFinish 0 (some 0)), .eff (.destPublish 1 (some 0)),
  .def 2 (.slotAddr 0), .def 3 (.snapshot .owner 2), .def 4 (.render 3 (some 0)),
  .eff (.print [.text "side"] (some 0)), .def 5 (.constInt .i64 0), .def 6 (.indexChecked 3 5 (some 0)),
  .def 7 (.constInt .u8 66), .eff (.store 6 7 (some 0)), .def 8 (.render 3 (some 0)),
  .eff (.print [.val 4,.val 8] (some 0)), .eff (.leave 0), .term (.ret [] none)]⟩]
  #[⟨byteTy,.mutable,0,0⟩]]

#guard (Validate.validate renderBeforeMutation).isOk
#guard observation renderBeforeMutation == some ("side\nAB\n".toUTF8.data.toList,
  [.begin 0,.write 0 0,.publish 0])
#guard roundTrip renderBeforeMutation

private def escapingRender : Module :=
  let entry := renderBeforeMutation.funcs[0]
  let block := entry.blocks[0]
  { renderBeforeMutation with funcs := #[{ entry with blocks := #[{ block with
    insts := (block.insts.take 14 ++ [.def 9 (.viewLen 4)] ++ block.insts.drop 14) }] }] }

#guard (match Validate.validate escapingRender with | .error v => v.code == .v060 | _ => false)

private def fixedSnapshot : Module := moduleOf #[
  function "entry" #[⟨[],[.eff (.enter 0), .def 0 (.destOpen (.slot 0) byteTy .value none (some 0)),
    .def 1 (.call 1 [] (some 0)), .eff (.destSnapshot 0 1 (some 0)), .def 2 (.destFinish 0 (some 0)),
    .eff (.destPublish 2 (some 0)), .def 3 (.slotAddr 0), .def 4 (.snapshot .owner 3),
    .eff (.print [.val 4] (some 0)), .eff (.leave 0), .term (.ret [] none)]⟩] #[⟨byteTy,.mutable,0,0⟩],
  function "snapshot" #[⟨[],[.def 0 (.constInt .u8 65), .def 1 (.constInt .u8 0), .def 2 (.constInt .u8 255),
    .def 3 (.arrLit (.arr (.int .u8) 3) [0,1,2]), .term (.ret [3] none)]⟩]
    #[] [⟨.arr (.int .u8) 3,.register,none⟩]]

#guard (Validate.validate fixedSnapshot).isOk
#guard observation fixedSnapshot == some ([65,0,255,10],[.begin 0,.write 0 0,.write 0 1,.write 0 2,.publish 0])
#guard roundTrip fixedSnapshot

private def fixedSnapshotAbort : Module :=
  let callee := function "snapshot" #[⟨[],[.def 0 (.constInt .u8 65), .term (.abort .userAbort (some 0))]⟩]
    #[] [⟨.arr (.int .u8) 3,.register,none⟩]
  { fixedSnapshot with funcs := #[fixedSnapshot.funcs[0],callee] }

#guard (Validate.validate fixedSnapshotAbort).isOk
#guard (match Run.run 1000 .release fixedSnapshotAbort with
  | .done (.aborted .userAbort 0) stdout events => stdout.isEmpty && events == [.begin 0]
  | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def descriptorCopy : Module :=
  let original := sliceBacking true
  let slice := Ty.slice .readOnly (.int .u8)
  let entry := function "entry" #[⟨[],[
    .eff (.enter 0), .def 0 (.globalAddr 0), .def 1 (.snapshot .owner 0),
    .def 2 (.viewSlice .readOnly 1 .omitted .omitted (some 0)), .eff (.slotInit 0 2 (some 0)),
    .def 3 (.slotAddr 0), .def 4 (.load 3), .def 5 (.sliceView 4),
    .def 6 (.destOpen (.slot 1) byteTy .value none (some 0)), .eff (.destCopy 6 5 (some 0)),
    .def 7 (.destFinish 6 (some 0)), .eff (.destPublish 7 (some 0)),
    .def 8 (.slotAddr 1), .def 9 (.snapshot .owner 8), .eff (.print [.val 9] (some 0)),
    .eff (.leave 0), .term (.ret [] none)]⟩] #[⟨slice,.immutable,0,0⟩,⟨byteTy,.mutable,0,1⟩]
  { original with funcs := #[entry] }

#guard (Validate.validate descriptorCopy).isOk
#guard observation descriptorCopy == some ([65,66,10],
  [.begin 0,.copy (.storage 1 []) 0,.write 0 0,.write 0 1,.publish 0])
#guard roundTrip descriptorCopy

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def repeatPrivate (count : Nat) : Module :=
  let resultTy := Ty.arr byteTy count
  moduleOf #[function "entry" #[⟨[],[
    .eff (.enter 0), .def 0 (.destOpen (.slot 0) resultTy .value none (some 0)),
    .def 1 (.destOpen (.slot 1) byteTy .value none (some 0)),
    .eff (.destBytes 1 [65,66] (some 0)), .def 2 (.destFinish 1 (some 0)),
    .eff (.destRepeat 0 2 (some 0)), .def 3 (.destFinish 0 (some 0)), .eff (.destPublish 3 (some 0)),
    .def 4 (.slotAddr 0), .def 5 (.snapshot .owner 4), .eff (.print [.val 5] (some 0)),
    .eff (.leave 0), .term (.ret [] none)]⟩]
    #[⟨resultTy,.immutable,0,0⟩,⟨byteTy,.immutable,0,1⟩]]

#guard (Validate.validate (repeatPrivate 2)).isOk
#guard observation (repeatPrivate 2) == some ("[\"AB\", \"AB\"]\n".toUTF8.data.toList,
  [.begin 0,.begin 1,.write 1 0,.write 1 1,.copy (.repeat 1) 0,.write 0 0,.copy (.repeat 1) 0,.write 0 1,.publish 0])
#guard roundTrip (repeatPrivate 2)
#guard (match Validate.validate (repeatPrivate 0) with | .error v => v.code == .v010 | _ => false)

private def reusedRepeatSource : Module :=
  let original := repeatPrivate 2
  let entry := original.funcs[0]
  let block := entry.blocks[0]
  { original with funcs := #[{ entry with blocks := #[{ block with
    insts := block.insts.take 6 ++ [.eff (.destRepeat 0 2 (some 0))] ++ block.insts.drop 6 }] }] }

#guard (match Validate.validate reusedRepeatSource with | .error v => v.code == .v060 | _ => false)

private def observedRepeatSource : Module :=
  let original := repeatPrivate 2
  let entry := original.funcs[0]
  let block := entry.blocks[0]
  { original with funcs := #[{ entry with blocks := #[{ block with
    insts := block.insts.take 5 ++ [.def 6 (.slotAddr 1),.def 7 (.snapshot .owner 6)] ++ block.insts.drop 5 }] }] }

#guard (match Validate.validate observedRepeatSource with | .error v => v.code == .v060 | _ => false)

private def reusedReceivingSlot : Module :=
  let entry := rawBytes.funcs[0]
  let block := entry.blocks[0]
  { rawBytes with funcs := #[{ entry with blocks := #[{ block with
    insts := block.insts.take 5 ++ [.def 2 (.destOpen (.slot 0) byteTy .value none (some 0)),
      .def 3 (.destFinish 2 (some 0)), .eff (.destPublish 3 (some 0)), .eff (.leave 0), .term (.ret [] none)] }] }] }

#guard (match Validate.validate reusedReceivingSlot with | .error v => v.code == .v060 | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def limitedBranch : Module :=
  let ty := Ty.limited (.int .u8) 1
  let entry := function "entry" #[⟨[],[
    .eff (.enter 0),.def 0 (.destOpen (.slot 0) ty .value none (some 0)),
    .def 1 (.constBool true),.term (.condbr 1 1 [0] 2 [0])]⟩,
    ⟨[(2,.dest ty .value)],[.eff (.destBytes 2 [65] (some 0)),.term (.br 3 [2])]⟩,
    ⟨[(3,.dest ty .value)],[.eff (.destBytes 3 [66] (some 0)),.term (.br 3 [3])]⟩,
    ⟨[(4,.dest ty .value)],[.def 5 (.destFinish 4 (some 0)),.eff (.destPublish 5 (some 0)),
      .def 6 (.slotAddr 0),.def 7 (.snapshot .owner 6),.eff (.print [.val 7] (some 0)),
      .eff (.leave 0),.term (.ret [] none)]⟩] #[⟨ty,.immutable,0,0⟩]
  moduleOf #[{ entry with summary := known [] [] [] false true }]

#guard (Validate.validate limitedBranch).isOk
#guard observation limitedBranch == some ([65,10],[.begin 0,.write 0 0,.publish 0])
#guard roundTrip limitedBranch

private def borrowedSliceWrongSlot : Module :=
  let original := sliceBacking true
  let callee := original.funcs[1]
  let block := callee.blocks[0]
  { original with funcs := #[original.funcs[0],{ callee with
    slots := #[⟨.int .u8,.immutable,0,0⟩,callee.slots[0]],
    blocks := #[{ block with insts := [.eff (.enter 0),.eff (.slotInit 1 0 (some 0))] ++ block.insts.drop 2 }] }] }

#guard (match Validate.validate borrowedSliceWrongSlot with | .error v => v.code == .v010 | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def writerRecursiveWire : String := "[\"module\",\"gir-h/0.4\",\"core-construction\",[[\"file\",\"t.goose\"]],[[\"int\",\"u8\"],[\"varr\",0],[\"arr\",1,2],[\"dest\",2,\"value\"],[\"dest\",1,\"value\"],[\"built\",1,\"value\"],[\"built\",2,\"value\"],[\"int\",\"i64\"],[\"view\",\"const\",0]],[],[],[],[[\"func\",\"main\",[],[],[[\"slot\",2,\"let\",0,0]],[[\"scope\",[]]],[[\"block\",[],[[\"x_enter\",0],[\"i_dest_open\",0,[\"dr_slot\",0],2,\"value\",[],[0]],[\"i_dest_child\",1,0,1,[0]],[\"x_dest_bytes\",1,[65,0],[0]],[\"i_dest_finish\",2,1,[0]],[\"x_dest_attach\",0,2,[0]],[\"i_dest_child\",3,0,1,[0]],[\"x_dest_bytes\",3,[255],[0]],[\"i_dest_finish\",4,3,[0]],[\"x_dest_attach\",0,4,[0]],[\"i_dest_finish\",5,0,[0]],[\"x_dest_publish\",5,[0]],[\"i_slot\",6,0],[\"i_snap\",7,\"borrowed\",6],[\"i_int\",8,7,\"0\"],[\"i_index\",9,7,8,[0]],[\"i_snap\",10,\"borrowed\",9],[\"i_render\",11,10,[0]],[\"x_print\",[[\"pp_val\",11]],[0]],[\"x_leave\",0],[\"t_ret\",[],[]]]]],[\"roots\",[],[],[]],[\"summary\",[],[],[],[],[],[],[],[],1,1],[],[]]],0,[[\"origin\",0,1,\"let\"]]]\n\n"

private def writerRecursive : Option Module := (Decode.decodeBytes writerRecursiveWire.toUTF8).toOption

#guard writerRecursive.any (fun module => (Validate.validate module).isOk)
#guard writerRecursive.bind observation == some ([65,0,10],
  [.begin 0,.begin 1,.write 1 0,.write 1 1,.write 0 0,.begin 2,.write 2 0,.write 0 1,.publish 0])
#guard writerRecursive.any roundTrip

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def publishBeforeFit : Module :=
  let original := staged 2
  let entry := original.funcs[0]
  let block := entry.blocks[0]
  { original with funcs := #[{ entry with blocks := #[{ block with insts := block.insts.map fun
    | .def 3 (.destFit ..) => .def 3 .constUnit
    | .eff (.destPublish 3 origin) => .eff (.destPublish 2 origin)
    | inst => inst }] }] }

#guard (match Validate.validate publishBeforeFit with | .error v => v.code == .v060 | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def fixedInitializerOrdinal : Module :=
  let array := Ty.arr (.int .u8) 2
  let entry := function "entry" #[⟨[],[
    .eff (.enter 0),.def 0 (.call 1 [] (some 0)),.eff (.slotInit 0 0 (some 0)),
    .def 1 (.slotAddr 0),.def 2 (.snapshot .owner 1),
    .def 3 (.destOpen (.slot 1) byteTy .value none (some 0)),.eff (.destCopy 3 2 (some 0)),
    .def 4 (.destFinish 3 (some 0)),.eff (.destPublish 4 (some 0)),
    .def 5 (.slotAddr 1),.def 6 (.snapshot .owner 5),.eff (.print [.val 6] (some 0)),
    .eff (.leave 0),.term (.ret [] none)]⟩] #[⟨array,.immutable,0,0⟩,⟨byteTy,.immutable,0,1⟩]
  let producer := function "initializer" #[⟨[],[
    .eff (.enter 0),.def 0 (.destOpen (.slot 0) byteTy .value none (some 0)),
    .eff (.destBytes 0 [88] (some 0)),.def 1 (.destFinish 0 (some 0)),.eff (.destPublish 1 (some 0)),
    .def 2 (.constInt .u8 65),.def 3 (.constInt .u8 66),.def 4 (.arrLit array [2,3]),
    .eff (.leave 0),.term (.ret [4] (some 0))]⟩] #[⟨byteTy,.immutable,0,0⟩] [⟨array,.register,none⟩]
  moduleOf #[entry,producer]

#guard (Validate.validate fixedInitializerOrdinal).isOk
#guard observation fixedInitializerOrdinal == some ([65,66,10],
  [.begin 0,.write 0 0,.publish 0,.begin 1,.copy (.storage 1 []) 1,.write 1 0,.write 1 1,.publish 1])
#guard roundTrip fixedInitializerOrdinal

private def parameterOrdinal : Module :=
  let slice := Ty.slice .readOnly (.int .u8)
  let entry := function "entry" #[⟨[],[.def 0 (.call 1 [] (some 0)),.def 1 (.bytes [65,66] (some 0)),
    .def 2 (.call 2 [0,1] (some 0)),.term (.ret [] none)]⟩]
  let source := function "argument" #[⟨[],[
    .eff (.enter 0),.def 0 (.destOpen (.slot 0) byteTy .value none (some 0)),
    .eff (.destBytes 0 [88] (some 0)),.def 1 (.destFinish 0 (some 0)),.eff (.destPublish 1 (some 0)),
    .def 2 (.constInt .i64 7),.eff (.leave 0),.term (.ret [2] (some 0))]⟩]
    #[⟨byteTy,.immutable,0,0⟩] [⟨.int .i64,.register,none⟩]
  let callee := function "parameter" #[⟨[(0,.data (.int .i64)),(1,.data slice)],[
    .eff (.enter 0),.eff (.slotInit 0 0 (some 0)),.eff (.slotInit 1 1 (some 0)),
    .def 2 (.sliceView 1),.def 3 (.destOpen (.slot 2) byteTy .value none (some 0)),
    .eff (.destCopy 3 2 (some 0)),.def 4 (.destFinish 3 (some 0)),.eff (.destPublish 4 (some 0)),
    .def 5 (.slotAddr 2),.def 6 (.snapshot .owner 5),.eff (.print [.val 6] (some 0)),
    .eff (.leave 0),.term (.ret [] none)]⟩]
    #[⟨.int .i64,.immutable,0,0⟩,⟨slice,.immutable,0,1⟩,⟨byteTy,.immutable,0,2⟩]
  moduleOf #[entry,source,{ callee with params := [.int .i64,slice], roots := { params := #[(1,[.static])] } }]

#guard (Validate.validate parameterOrdinal).isOk
#guard observation parameterOrdinal == some ([65,66,10],
  [.begin 0,.write 0 0,.publish 0,.begin 1,.copy (.storage 2 []) 1,.write 1 0,.write 1 1,.publish 1])
#guard roundTrip parameterOrdinal

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def fixedGlobalOrdinal : Module :=
  let array := Ty.arr (.int .u8) 2
  let entry := function "entry" #[⟨[],[
    .eff (.enter 0),.def 0 (.globalAddr 0),.def 1 (.snapshot .owner 0),
    .def 2 (.destOpen (.slot 0) byteTy .value none (some 0)),.eff (.destCopy 2 1 (some 0)),
    .def 3 (.destFinish 2 (some 0)),.eff (.destPublish 3 (some 0)),
    .def 4 (.slotAddr 0),.def 5 (.snapshot .owner 4),.eff (.print [.val 5] (some 0)),
    .eff (.leave 0),.term (.ret [] none)]⟩] #[⟨byteTy,.immutable,0,0⟩]
  { (moduleOf #[entry]) with globals := #[⟨"fixed",array,.immutable,fixedInitializerOrdinal.funcs[1],0⟩] }

#guard (Validate.validate fixedGlobalOrdinal).isOk
#guard observation fixedGlobalOrdinal == observation fixedInitializerOrdinal
#guard roundTrip fixedGlobalOrdinal

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def overlappingTargets : Module :=
  let entry := function "entry" #[⟨[],[
    .eff (.enter 0),.def 0 (.destOpen (.slot 0) byteTy .value none (some 0)),
    .def 1 (.callConstruct 1 [] [0] (some 0)),.eff (.destPublish 1 (some 0)),
    .def 2 (.slotAddr 0),.def 3 (.snapshot .owner 2),.eff (.print [.val 3] (some 0)),
    .eff (.leave 0),.term (.ret [] none)]⟩] #[⟨byteTy,.immutable,0,0⟩]
  let member := function "member" #[⟨[(0,.dest byteTy .value)],[
      .def 1 (.constBool true),.term (.invoke 2 [1] [] 1 [] [⟨0,2,[]⟩,⟨1,3,[]⟩] (some 0))]⟩,
    ⟨[],[.term (.abort .userAbort (some 0))]⟩,
    ⟨[(2,.built byteTy .value)],[.def 3 (.destAbandon 0 (some 0)),.eff (.destCancel 3 (some 0)),
      .def 4 (.destRelocate 2 .exitValue (some 0)),.eff (.print [.text "zero"] (some 0)),.term (.ret [4] (some 0))]⟩,
    ⟨[(5,.built byteTy .value)],[.def 6 (.destAbandon 0 (some 0)),.eff (.destCancel 6 (some 0)),
      .def 7 (.destRelocate 5 .exitValue (some 0)),.eff (.print [.text "one"] (some 0)),.term (.ret [7] (some 0))]⟩]
    #[] [⟨byteTy,.value,none⟩]
  let helper := function "helper" #[⟨[(0,.data .bool)],[.term (.condbr 0 1 [] 2 [])]⟩,
    ⟨[],[.def 1 (.targetDest 1 0 (some 0)),.eff (.destBytes 1 [65] (some 0)),
      .def 2 (.destFinish 1 (some 0)),.term (.escape 1 [2] [] (some 0))]⟩,
    ⟨[],[.def 3 (.targetDest 0 0 (some 0)),.eff (.destBytes 3 [66] (some 0)),
      .def 4 (.destFinish 3 (some 0)),.term (.escape 0 [4] [] (some 0))]⟩]
  let other := function "other" #[⟨[(0,.dest byteTy .value)],[.eff (.destBytes 0 [67] (some 0)),
    .def 1 (.destFinish 0 (some 0)),.term (.ret [1] (some 0))]⟩] #[] [⟨byteTy,.value,none⟩]
  { (moduleOf #[{ entry with summary := known [] [] [] true true },
      { member with summary := known [0] [] [] true true },
      { helper with params := [.bool], summary := known [] [0,1] [0,1] false false },
      { other with summary := known [0] [] [] false false }]) with targets := #[⟨1,[]⟩,⟨1,[3]⟩] }

#guard (Validate.validate overlappingTargets).isOk
#guard observation overlappingTargets == some ("one\nA\n".toUTF8.data.toList,
  [.begin 0,.write 0 0,.publish 0])
#guard roundTrip overlappingTargets

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def invokeReferenceRoots : Module :=
  let array := Ty.arr (.int .u8) 2
  let reference := Ty.ref .readOnly array
  let entry := function "entry" #[⟨[],[.def 0 (.call 1 [] (some 0)),
    .def 1 (.snapshot .borrowed 0),.eff (.print [.val 1] (some 0)),.term (.ret [] none)]⟩]
  let member := function "member" #[⟨[],[.def 0 (.constBool true),
      .term (.invoke 2 [0] [] 1 [] [⟨0,2,[]⟩] (some 0))]⟩,
    ⟨[(1,.data reference)],[.term (.ret [1] (some 0))]⟩,
    ⟨[(2,.data reference)],[.term (.ret [2] (some 0))]⟩] #[] [⟨reference,.register,none⟩]
  let helper := function "helper" #[⟨[(0,.data .bool)],[.term (.condbr 0 1 [] 2 [])]⟩,
    ⟨[],[.def 1 (.globalAddr 0),.term (.ret [1] (some 0))]⟩,
    ⟨[],[.def 2 (.globalAddr 1),.term (.escape 0 [2] [] (some 0))]⟩] #[] [⟨reference,.register,none⟩]
  let initializer := function "initializer" #[⟨[],[.def 0 (.constInt .u8 65),.def 1 (.constInt .u8 66),
    .def 2 (.arrLit array [0,1]),.term (.ret [2] (some 0))]⟩] #[] [⟨array,.register,none⟩]
  let second := function "second" #[⟨[],[.def 0 (.constInt .u8 67),.def 1 (.constInt .u8 68),
    .def 2 (.arrLit array [0,1]),.term (.ret [2] (some 0))]⟩] #[] [⟨array,.register,none⟩]
  { (moduleOf #[{ entry with summary := .known ⟨[.global 0,.global 1],[],[],[],[],[],[],[],false,true⟩ },
      { member with roots := { results := #[[.global 0,.global 1]] }, summary := known },
      { helper with params := [.bool], roots := { results := #[[.global 0]] }, summary := known [] [0] [0] }]) with
    globals := #[⟨"a",array,.immutable,initializer,0⟩,⟨"b",array,.immutable,second,0⟩],
    targets := #[⟨1,[]⟩] }

#guard (Validate.validate invokeReferenceRoots).isOk
#guard observation invokeReferenceRoots == some ([65,66,10],[])
#guard roundTrip invokeReferenceRoots

private def invokeReferenceEscape : Module :=
  { invokeReferenceRoots with funcs := invokeReferenceRoots.funcs.mapIdx fun index f =>
    if index == 1 then { f with blocks := f.blocks.map fun block => { block with insts := block.insts.map fun
      | .def result (.constBool _) => .def result (.constBool false)
      | inst => inst } } else f }

#guard (Validate.validate invokeReferenceEscape).isOk
#guard observation invokeReferenceEscape == some ("CD\n".toUTF8.data.toList,[])
#guard roundTrip invokeReferenceEscape

private def omittedInvokeRoot (global : Nat) : Module :=
  let original := invokeReferenceRoots
  { original with funcs := original.funcs.mapIdx fun index f =>
    if index == 1 then { f with roots := { f.roots with results := #[[.global global]] } } else f }

#guard (match Validate.validate (omittedInvokeRoot 0) with | .error v => v.code == .v050 | _ => false)
#guard (match Validate.validate (omittedInvokeRoot 1) with | .error v => v.code == .v050 | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def resultPackRoots : Module :=
  let original := invokeReferenceRoots
  let array := Ty.arr (.int .u8) 2
  let descriptor : ResultDescriptor := ⟨.ref .readOnly array,.register,none⟩
  let entry := function "entry" #[⟨[],[.def 0 (.call 2 [] (some 0)),.def 1 (.result 0 0),.def 2 (.result 0 1),
    .def 3 (.snapshot .borrowed 1),.def 4 (.snapshot .borrowed 2),
    .eff (.print [.val 3,.val 4] (some 0)),.term (.ret [] none)]⟩]
  let producer := function "pair" #[⟨[],[.def 0 (.globalAddr 0),.def 1 (.globalAddr 1),
    .term (.ret [0,1] (some 0))]⟩] #[] [descriptor,descriptor]
  let forward := function "forward" #[⟨[],[.def 0 (.call 1 [] (some 0)),.term (.br 1 [0])]⟩,
    ⟨[(1,.pack [descriptor,descriptor])],[.def 2 (.result 1 0),.def 3 (.result 1 1),.term (.ret [2,3] (some 0))]⟩]
    #[] [descriptor,descriptor]
  { original with funcs := #[
    { entry with summary := .known ⟨[.global 0,.global 1],[],[],[],[],[],[],[],false,true⟩ },
    { producer with roots := { results := #[[.global 0],[.global 1]] }, summary := known },
    { forward with roots := { results := #[[.global 0],[.global 1]] }, summary := known }], targets := #[] }

#guard (Validate.validate resultPackRoots).isOk
#guard observation resultPackRoots == some ("ABCD\n".toUTF8.data.toList,[])
#guard roundTrip resultPackRoots

private def missingPackRoot : Module :=
  { resultPackRoots with funcs := resultPackRoots.funcs.mapIdx fun index f =>
    if index == 2 then { f with roots := { f.roots with results := #[[],[.global 1]] } } else f }

#guard (match Validate.validate missingPackRoot with | .error v => v.code == .v050 | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def borrowedSliceSlotLoad : Module :=
  let original := sliceBacking true
  let callee := original.funcs[1]
  { original with funcs := #[original.funcs[0],{ callee with blocks := #[⟨[(0,.data callee.params[0])],[
    .eff (.enter 0),.eff (.slotInit 0 0 (some 0)),.def 1 (.slotAddr 0),.def 2 (.load 1),
    .def 3 (.load 2),.def 4 (.sliceView 3),.eff (.print [.val 4] (some 0)),
    .eff (.leave 0),.term (.ret [] none)]⟩] }] }

#guard (Validate.validate borrowedSliceSlotLoad).isOk
#guard observation borrowedSliceSlotLoad == some ([65,66,10],[])
#guard roundTrip borrowedSliceSlotLoad

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def writerCallWire : String := "[\"module\",\"gir-h/0.4\",\"core-construction\",[[\"file\",\"t.goose\"]],[[\"int\",\"i64\"],[\"grow\",0],[\"dest\",1,\"value\"],[\"built\",1,\"value\"]],[],[],[],[[\"func\",\"main\",[],[],[[\"slot\",1,\"let\",0,0]],[[\"scope\",[]]],[[\"block\",[],[[\"x_enter\",0],[\"i_int\",0,0,\"1\"],[\"i_dest_open\",1,[\"dr_slot\",0],1,\"value\",[0],[0]],[\"i_call_construct\",2,1,[],[1],[0]],[\"x_dest_publish\",2,[0]],[\"x_leave\",0],[\"t_ret\",[],[]]]]],[\"roots\",[],[],[]],[\"summary\",[],[],[],[],[],[],[],[],0,0],[],[]],[\"func\",\"make\",[],[[\"result\",1,\"value\",[]]],[],[[\"scope\",[]]],[[\"block\",[[\"bp\",0,2]],[[\"x_enter\",0],[\"i_int\",1,0,\"7\"],[\"x_dest_write\",0,1,[0]],[\"i_dest_finish\",2,0,[0]],[\"x_leave\",0],[\"t_ret\",[2],[0]]]]],[\"roots\",[],[],[[]]],[\"summary\",[],[],[],[],[],[0],[],[],0,0],[],[]]],0,[[\"origin\",0,1,\"let\"]]]\n\n"

private def writerCall : Option Module := (Decode.decodeBytes writerCallWire.toUTF8).toOption

#guard writerCall.any (fun module => (Validate.validate module).isOk)
#guard writerCall.bind observation == some ([],[.begin 0,.write 0 0,.publish 0])
#guard writerCall.any roundTrip

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def reboundGlobalRoots : Module :=
  let original := invokeReferenceRoots
  let slice := Ty.slice .readOnly (.int .u8)
  let initializer := function "descriptor" #[⟨[],[.def 0 (.globalAddr 0),.def 1 (.snapshot .borrowed 0),
    .def 2 (.viewSlice .readOnly 1 .omitted .omitted (some 0)),.term (.ret [2] (some 0))]⟩] #[] [⟨slice,.register,none⟩]
  let entry := function "entry" #[⟨[],[.def 0 (.globalAddr 1),.def 1 (.snapshot .borrowed 0),
    .def 2 (.viewSlice .readOnly 1 .omitted .omitted (some 0)),.def 3 (.globalAddr 2),
    .eff (.store 3 2 (some 0)),.def 4 (.call 1 [] (some 0)),.term (.ret [] none)]⟩]
  let reader := function "reader" #[⟨[],[.def 0 (.globalAddr 2),.def 1 (.load 0),.def 2 (.sliceView 1),
    .eff (.print [.val 2] (some 0)),.term (.ret [] none)]⟩]
  { original with
    funcs := #[
      { entry with summary := .known ⟨[.global 0,.global 1,.global 2],[.global 2],[],[],[],[],[],[],true,true⟩ },
      { reader with summary := .known ⟨[.global 0,.global 1,.global 2],[],[],[],[],[],[],[],false,true⟩ }],
    globals := original.globals ++ #[⟨"descriptor",slice,.mutable,
      { initializer with
        roots := { results := #[[.global 0]] },
        summary := .known ⟨[.global 0],[],[],[],[],[],[],[],true,false⟩ },0⟩], targets := #[] }

#guard (Validate.validate reboundGlobalRoots).isOk
#guard observation reboundGlobalRoots == some ("CD\n".toUTF8.data.toList,[])
#guard roundTrip reboundGlobalRoots

private def omittedReboundGlobalRoot : Module :=
  { reboundGlobalRoots with funcs := reboundGlobalRoots.funcs.mapIdx fun index f =>
    if index == 1 then { f with summary := .known ⟨[.global 0,.global 2],[],[],[],[],[],[],[],false,true⟩ } else f }

#guard (match Validate.validate omittedReboundGlobalRoot with | .error v => v.code == .v050 | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def sliceParameterRebind : Module :=
  let original := sliceBacking true
  let slice := Ty.slice .readOnly (.int .u8)
  let entry := original.funcs[0]
  let callee := function "rebind" #[⟨[(0,.data (.ref .mutable slice))],[
    .eff (.enter 0),.eff (.slotInit 0 0 (some 0)),.def 1 (.bytes [67,68] (some 0)),
    .eff (.store 0 1 (some 0)),.eff (.leave 0),.term (.ret [] none)]⟩]
    #[⟨.ref .mutable slice,.immutable,0,0⟩]
  { original with funcs := #[{ entry with slots := #[⟨slice,.mutable,0,0⟩] },
    { callee with
      params := [.ref .mutable slice],
      roots := { params := #[(0,[.param 0])], contents := #[(0,[.global 0,.static])] },
      summary := .known ⟨[],[.param 0],[],[],[.param 0],[],[],[],false,false⟩ }] }

#guard (Validate.validate sliceParameterRebind).isOk
#guard observation sliceParameterRebind == some ([],[])
#guard roundTrip sliceParameterRebind

private def omittedParameterRebind : Module :=
  { sliceParameterRebind with funcs := sliceParameterRebind.funcs.mapIdx fun index f =>
    if index == 1 then { f with summary := .known ⟨[],[.param 0],[],[],[],[],[],[],false,false⟩ } else f }

#guard (match Validate.validate omittedParameterRebind with | .error v => v.code == .v050 | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def specializedParameterEffect : Module :=
  let original := invokeReferenceRoots
  let array := Ty.arr (.int .u8) 2
  let reference := Ty.ref .readOnly array
  let entry := function "entry" #[⟨[],[.def 0 (.globalAddr 0),.def 1 (.call 1 [0] (some 0)),.term (.ret [] none)]⟩]
  let callee := function "specialized" #[⟨[(0,.data reference)],[
    .eff (.enter 0),.eff (.slotInit 0 0 (some 0)),.def 1 (.snapshot .borrowed 0),
    .eff (.print [.val 1] (some 0)),.eff (.leave 0),.term (.ret [] none)]⟩] #[⟨reference,.immutable,0,0⟩]
  { original with funcs := #[
    { entry with summary := .known ⟨[.global 0],[],[],[],[],[],[],[],false,true⟩ },
    { callee with
      params := [reference], roots := { params := #[(0,[.global 0])] },
      summary := .known ⟨[.param 0],[],[],[],[],[],[],[],false,true⟩ }], targets := #[] }

#guard (Validate.validate specializedParameterEffect).isOk
#guard observation specializedParameterEffect == some ("AB\n".toUTF8.data.toList,[])
#guard roundTrip specializedParameterEffect

private def omittedSpecializedParameterEffect : Module :=
  { specializedParameterEffect with funcs := specializedParameterEffect.funcs.mapIdx fun index f =>
    if index == 1 then { f with summary := known [] [] [] false true } else f }

#guard (match Validate.validate omittedSpecializedParameterEffect with | .error v => v.code == .v050 | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def returnedReboundSlice : Module :=
  let original := invokeReferenceRoots
  let slice := Ty.slice .readOnly (.int .u8)
  let entry := function "entry" #[⟨[],[.def 0 (.call 1 [] (some 0)),.def 1 (.sliceView 0),
    .eff (.print [.val 1] (some 0)),.term (.ret [] none)]⟩]
  let wrapper := function "wrapper" #[⟨[],[
    .eff (.enter 0),.def 0 (.globalAddr 0),.def 1 (.snapshot .borrowed 0),
    .def 2 (.viewSlice .readOnly 1 .omitted .omitted (some 0)),.eff (.slotInit 0 2 (some 0)),
    .def 3 (.slotAddr 0),.def 4 (.call 2 [3] (some 0)),.def 5 (.load 3),
    .eff (.leave 0),.term (.ret [5] (some 0))]⟩] #[⟨slice,.mutable,0,0⟩] [⟨slice,.register,none⟩]
  let callee := function "rebind" #[⟨[(0,.data (.ref .mutable slice))],[
    .eff (.enter 0),.eff (.slotInit 0 0 (some 0)),.def 1 (.globalAddr 1),.def 2 (.snapshot .borrowed 1),
    .def 3 (.viewSlice .readOnly 2 .omitted .omitted (some 0)),.eff (.store 0 3 (some 0)),
    .eff (.leave 0),.term (.ret [] none)]⟩] #[⟨.ref .mutable slice,.immutable,0,0⟩]
  { original with funcs := #[
    { entry with summary := .known ⟨[.global 0,.global 1],[],[],[],[],[],[],[],true,true⟩ },
    { wrapper with
      roots := { results := #[[.global 0,.global 1]] },
      summary := .known ⟨[.global 0,.global 1],[],[],[],[],[],[],[],true,false⟩ },
    { callee with
      params := [.ref .mutable slice], roots := { params := #[(0,[.param 0])], contents := #[(0,[.global 0,.global 1])] },
      summary := .known ⟨[.global 1],[.param 0],[],[],[.param 0],[],[],[],true,false⟩ }], targets := #[] }

#guard (Validate.validate returnedReboundSlice).isOk
#guard observation returnedReboundSlice == some ("CD\n".toUTF8.data.toList,[])
#guard roundTrip returnedReboundSlice

private def omittedReturnedReboundRoot : Module :=
  { returnedReboundSlice with funcs := returnedReboundSlice.funcs.mapIdx fun index f =>
    if index == 1 then { f with roots := { f.roots with results := #[[.global 0]] } } else f }

#guard (match Validate.validate omittedReturnedReboundRoot with | .error v => v.code == .v050 | _ => false)

private def omittedStoredBackingRoot : Module :=
  { returnedReboundSlice with funcs := returnedReboundSlice.funcs.mapIdx fun index f =>
    if index == 2 then { f with roots := { f.roots with contents := #[(0,[.global 0])] } } else f }

#guard (match Validate.validate omittedStoredBackingRoot with | .error v => v.code == .v050 | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def initializerNeedsTarget : Module :=
  let original := invokeReferenceRoots
  let initializer := original.globals[0].init
  let array := Ty.arr (.int .u8) 2
  let helper := function "requires_target" #[⟨[],[.def 0 (.globalAddr 0),.term (.escape 0 [0] [] (some 0))]⟩]
  let initializer := { initializer with blocks := #[
    ⟨[],[.term (.invoke 3 [] [] 1 [] [⟨0,2,[]⟩] (some 0))]⟩,
    ⟨[],[.def 0 (.constInt .u8 65),.def 1 (.constInt .u8 66),.def 2 (.arrLit array [0,1]),.term (.ret [2] (some 0))]⟩,
    ⟨[(3,.data (.ref .readOnly array))],[.term (.escape 0 [3] [] (some 0))]⟩] }
  { original with
    globals := #[{ original.globals[0] with init := initializer },original.globals[1]],
    funcs := original.funcs ++ #[{ helper with summary := known [] [0] [0] }] }

#guard (match Validate.validate initializerNeedsTarget with | .error v => v.code == .v070 | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def renderedRepeatSource : Module :=
  let original := repeatPrivate 2
  let entry := original.funcs[0]
  let block := entry.blocks[0]
  { original with funcs := #[{ entry with blocks := #[{ block with
    insts := block.insts.take 5 ++ [.def 6 (.slotAddr 1),.def 7 (.render 6 (some 0)),
      .eff (.print [.val 7] (some 0))] ++ block.insts.drop 5 }] }] }

#guard (match Validate.validate renderedRepeatSource with | .error v => v.code == .v060 | _ => false)

private def competingAppend : Module :=
  let ty := Ty.grow (.int .u8)
  moduleOf #[function "entry" #[⟨[],[
    .eff (.enter 0),.def 0 (.destOpen (.slot 0) ty .value none (some 0)),
    .def 1 (.destFinish 0 (some 0)),.eff (.destPublish 1 (some 0)),.def 2 (.slotAddr 0),
    .def 3 (.destOpen (.append 2) byteTy .elementRun none (some 0)),
    .def 4 (.destOpen (.append 2) byteTy .elementRun none (some 0)),
    .def 5 (.destFinish 4 (some 0)),.eff (.destPublish 5 (some 0)),
    .def 6 (.destFinish 3 (some 0)),.eff (.destPublish 6 (some 0)),
    .eff (.leave 0),.term (.ret [] none)]⟩] #[⟨ty,.mutable,0,0⟩]]

#guard (match Validate.validate competingAppend with | .error v => v.code == .v060 | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def unmaterializedCopy : Module := moduleOf #[function "entry" #[⟨[],[
  .eff (.enter 0),.def 0 (.destOpen (.slot 0) byteTy .value none (some 0)),
  .def 1 (.bytes [65,66] (some 0)),.def 2 (.sliceView 1),.eff (.destCopy 0 2 (some 0)),
  .def 3 (.destFinish 0 (some 0)),.eff (.destPublish 3 (some 0)),
  .eff (.leave 0),.term (.ret [] none)]⟩] #[⟨byteTy,.immutable,0,0⟩]]

#guard (match Validate.validate unmaterializedCopy with | .error v => v.code == .v060 | _ => false)

private def sliceReferenceResult : Module :=
  let slice := Ty.slice .readOnly (.int .u8)
  let producer := function "parameter_type_result" #[⟨[(0,.data (.ref .readOnly slice))],[
    .eff (.enter 0),.eff (.slotInit 0 0 (some 0)),.eff (.leave 0),.term (.ret [0] (some 0))]⟩]
    #[⟨.ref .readOnly slice,.immutable,0,0⟩] [⟨.ref .readOnly slice,.register,none⟩]
  moduleOf #[function "entry" #[⟨[],[.term (.ret [] none)]⟩],
    { producer with params := [.ref .readOnly slice], roots := { params := #[(0,[.param 0])], results := #[[.param 0]] } }]

#guard (match Validate.validate sliceReferenceResult with | .error v => v.code == .v010 | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def emittedRawWire : String := "[\"module\",\"gir-h/0.4\",\"core-construction\",[[\"file\",\"construction_raw_bytes.goose\"]],[[\"int\",\"u8\"],[\"grow\",0],[\"int\",\"i64\"],[\"dest\",1,\"value\"],[\"built\",1,\"value\"],[\"tuple\",[4,2]],[\"view\",\"const\",0]],[],[],[],[[\"func\",\"main\",[],[],[[\"slot\",1,\"let\",0,0],[\"slot\",2,\"let\",0,1]],[[\"scope\",[]]],[[\"block\",[],[[\"x_enter\",0],[\"i_dest_open\",0,[\"dr_slot\",0],1,\"value\",[],[0]],[\"i_int\",1,0,\"65\"],[\"i_int\",2,0,\"66\"],[\"i_call_construct\",3,1,[1,2],[0],[0]],[\"i_result\",4,3,0],[\"i_result\",5,3,1],[\"x_dest_publish\",4,[0]],[\"x_init\",1,5,[0]],[\"i_slot\",6,0],[\"i_snap\",7,\"owner\",6],[\"i_render\",8,7,[2]],[\"x_print\",[[\"pp_val\",8]],[2]],[\"i_slot\",9,1],[\"i_load\",10,9],[\"t_exit\",10,[3]]]]],[\"roots\",[],[],[]],[\"summary\",[],[],[],[],[],[],[],[],1,1],[0],[]],[\"func\",\"payload\",[0,0],[[\"result\",1,\"value\",[2]],[\"result\",2,\"register\",[]]],[[\"slot\",0,\"let\",0,0],[\"slot\",0,\"let\",0,1],[\"slot\",1,\"var\",0,2]],[[\"scope\",[]]],[[\"block\",[[\"bp\",0,0],[\"bp\",1,0],[\"bp\",2,3]],[[\"x_enter\",0],[\"x_init\",0,0,[4]],[\"x_init\",1,1,[4]],[\"i_slot\",3,0],[\"i_load\",4,3],[\"x_dest_write\",2,4,[5]],[\"i_int\",5,0,\"0\"],[\"x_dest_write\",2,5,[5]],[\"i_int\",6,0,\"255\"],[\"x_dest_write\",2,6,[5]],[\"i_slot\",7,1],[\"i_load\",8,7],[\"x_dest_write\",2,8,[5]],[\"i_dest_finish\",9,2,[5]],[\"x_dest_bind\",2,9,[5]],[\"i_dest_named\",10,2,[7]],[\"i_int\",11,2,\"19\"],[\"x_leave\",0],[\"t_ret\",[10,11],[7]]]]],[\"roots\",[],[],[[],[]]],[\"summary\",[],[],[],[],[],[0],[],[],0,0],[4],[]]],0,[[\"origin\",0,9,\"let\"],[\"origin\",0,10,\"call\"],[\"origin\",0,11,\"print\"],[\"origin\",0,12,\"exit\"],[\"origin\",0,2,\"param\"],[\"origin\",0,3,\"let\"],[\"origin\",0,3,\"expr\"],[\"origin\",0,4,\"return\"]]]\n"

private def emittedRaw : Option Module := (Decode.decodeBytes emittedRawWire.toUTF8).toOption

#guard emittedRaw.any (fun module => (Validate.validate module).isOk)
#guard emittedRaw.any (fun module => Writer.write module == emittedRawWire)
#guard emittedRaw.any (fun module => match Run.run 1000 .release module with
  | .done (.exited 19) stdout events => stdout.data.toList == [65,0,255,66,10] &&
      events == [.begin 0,.write 0 0,.write 0 1,.write 0 2,.write 0 3,.publish 0]
  | _ => false)

private def emittedValuesWire : String := "[\"module\",\"gir-h/0.4\",\"core-construction\",[[\"file\",\"sem_construction_source_values.goose\"]],[[\"int\",\"i64\"],[\"grow\",0],[\"arr\",0,2],[\"dest\",1,\"value\"],[\"built\",1,\"value\"],[\"int\",\"u8\"],[\"view\",\"const\",5],[\"ref\",\"mut\",1]],[],[],[],[[\"func\",\"main\",[],[],[[\"slot\",1,\"var\",0,0],[\"slot\",2,\"let\",0,1],[\"slot\",2,\"let\",0,2],[\"slot\",0,\"let\",0,3],[\"slot\",0,\"let\",0,4],[\"slot\",0,\"let\",3,5]],[[\"scope\",[]],[\"scope\",[0]],[\"scope\",[0]],[\"scope\",[0]]],[[\"block\",[],[[\"x_enter\",0],[\"i_int\",0,0,\"1\"],[\"i_dest_open\",1,[\"dr_slot\",0],1,\"value\",[0],[0]],[\"i_int\",2,0,\"1\"],[\"x_dest_write\",1,2,[0]],[\"i_dest_finish\",3,1,[0]],[\"x_dest_publish\",3,[0]],[\"i_int\",4,0,\"2\"],[\"i_int\",5,0,\"3\"],[\"i_arr\",6,2,[4,5]],[\"x_init\",1,6,[1]],[\"i_int\",7,0,\"4\"],[\"i_fill\",8,2,7],[\"x_init\",2,8,[2]],[\"i_bool\",9,1],[\"t_condbr\",9,1,[],2,[]]]],[\"block\",[],[[\"x_enter\",1],[\"i_slot\",10,1],[\"i_snap\",11,\"owner\",10],[\"i_int\",12,0,\"0\"],[\"i_index\",13,11,12,[9]],[\"i_load\",14,13],[\"x_leave\",1],[\"t_br\",3,[14]]]],[\"block\",[],[[\"x_enter\",2],[\"i_int\",15,0,\"0\"],[\"x_leave\",2],[\"t_br\",3,[15]]]],[\"block\",[[\"bp\",16,0]],[[\"x_init\",3,16,[3]],[\"x_enter\",3],[\"i_int\",17,0,\"6\"],[\"x_init\",5,17,[5]],[\"i_slot\",18,5],[\"i_load\",19,18],[\"i_slot\",20,3],[\"i_load\",21,20],[\"i_bin\",22,\"add\",0,19,21,[11]],[\"x_leave\",3],[\"x_init\",4,22,[4]],[\"i_dest_open\",23,[\"dr_arg\",1,0],1,\"value\",[],[14]],[\"i_slot\",24,0],[\"x_dest_copy\",23,24,[13]],[\"i_dest_finish\",25,23,[13]],[\"i_dest_arg\",26,25,[14]],[\"i_call\",27,1,[26],[14]],[\"i_render\",28,27,[16]],[\"i_slot\",29,2],[\"i_snap\",30,\"owner\",29],[\"i_int\",31,0,\"1\"],[\"i_index\",32,30,31,[15]],[\"i_load\",33,32],[\"i_render\",34,33,[16]],[\"i_slot\",35,4],[\"i_load\",36,35],[\"i_render\",37,36,[16]],[\"x_print\",[[\"pp_val\",28],[\"pp_text\",\" \"],[\"pp_val\",34],[\"pp_text\",\" \"],[\"pp_val\",37]],[16]],[\"i_slot\",38,0],[\"i_slot\",39,4],[\"i_load\",40,39],[\"i_push\",41,38,40,[17]],[\"i_slot\",42,0],[\"i_snap\",43,\"owner\",42],[\"i_int\",44,0,\"1\"],[\"i_index\",45,43,44,[18]],[\"i_load\",46,45],[\"i_render\",47,46,[19]],[\"x_print\",[[\"pp_val\",47]],[19]],[\"x_leave\",0],[\"t_ret\",[],[0]]]]],[\"roots\",[],[],[]],[\"summary\",[],[],[],[],[],[],[],[],1,1],[0],[]],[\"func\",\"length\",[1],[[\"result\",0,\"register\",[]]],[[\"slot\",1,\"let\",0,0]],[[\"scope\",[]]],[[\"block\",[[\"bp\",0,7]],[[\"x_enter\",0],[\"x_init\",0,0,[20]],[\"i_slot\",1,0],[\"i_snap\",2,\"owner\",1],[\"i_vlen\",3,2],[\"x_leave\",0],[\"t_ret\",[3],[21]]]]],[\"roots\",[],[],[[]]],[\"summary\",[],[],[],[],[],[],[],[],0,0],[20],[]]],0,[[\"origin\",0,6,\"let\"],[\"origin\",0,7,\"let\"],[\"origin\",0,8,\"let\"],[\"origin\",0,9,\"let\"],[\"origin\",0,14,\"let\"],[\"origin\",0,15,\"let\"],[\"origin\",0,6,\"expr\"],[\"origin\",0,7,\"expr\"],[\"origin\",0,8,\"expr\"],[\"origin\",0,10,\"index\"],[\"origin\",0,9,\"expr\"],[\"origin\",0,16,\"binary\"],[\"origin\",0,14,\"expr\"],[\"origin\",0,18,\"expr\"],[\"origin\",0,18,\"call\"],[\"origin\",0,18,\"index\"],[\"origin\",0,18,\"print\"],[\"origin\",0,19,\"expr\"],[\"origin\",0,20,\"index\"],[\"origin\",0,20,\"print\"],[\"origin\",0,1,\"param\"],[\"origin\",0,2,\"return\"]]]\n"

#guard (Decode.decodeBytes emittedValuesWire.toUTF8).toOption.any (fun module =>
  (Validate.validate module).isOk && Writer.write module == emittedValuesWire)

private def repeatedOwnedProjection : Module :=
  let module := emittedRaw.getD rawBytes
  { module with funcs := module.funcs.mapIdx fun index f =>
    if index == 0 then { f with blocks := f.blocks.map fun block =>
      { block with insts := block.insts.flatMap fun inst =>
        match inst with
        | .def 5 (.result 3 1) => [inst,.def 11 (.result 3 0)]
        | _ => [inst] } } else f }

#guard (match Validate.validate repeatedOwnedProjection with | .error v => v.code == .v060 | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def publishedPushReference : Module :=
  let owner := Ty.grow byteTy
  moduleOf #[function "entry" #[⟨[],[
    .eff (.enter 0),.def 0 (.destOpen (.slot 0) owner .value none (some 0)),
    .def 1 (.destFinish 0 (some 0)),.eff (.destPublish 1 (some 0)),.def 2 (.slotAddr 0),
    .def 3 (.destOpen (.push 2) byteTy .value none (some 0)),.eff (.destBytes 3 [65,66] (some 0)),
    .def 4 (.destFinish 3 (some 0)),.def 5 (.destPublishRef 4 (some 0)),
    .def 6 (.snapshot .borrowed 5),.def 7 (.constInt .i64 0),.def 8 (.indexChecked 6 7 (some 0)),
    .def 9 (.constInt .u8 90),.eff (.store 8 9 (some 0)),
    .def 10 (.snapshot .owner 2),.eff (.print [.val 10] (some 0)),
    .eff (.leave 0),.term (.ret [] none)]⟩] #[⟨owner,.mutable,0,0⟩]]

#guard (Validate.validate publishedPushReference).isOk
#guard observation publishedPushReference == some ("[\"ZB\"]\n".toUTF8.data.toList,
  [.begin 0,.publish 0,.begin 1,.write 1 0,.write 1 1,.publish 1])
#guard roundTrip publishedPushReference

private def publishOrdinaryReference : Module :=
  { rawBytes with funcs := rawBytes.funcs.map fun f => { f with blocks := f.blocks.map fun block =>
    { block with insts := block.insts.map fun
      | .eff (.destPublish built org) => .def 4 (.destPublishRef built org)
      | inst => inst } } }

#guard (match Validate.validate publishOrdinaryReference with | .error v => v.code == .v060 | _ => false)

private def reusedPushReference : Module :=
  { publishedPushReference with funcs := publishedPushReference.funcs.map fun f => { f with blocks := f.blocks.map fun block =>
    { block with insts := block.insts.flatMap fun
      | .def 5 op => [.def 5 op,.def 11 (.destPublishRef 4 (some 0))]
      | inst => [inst] } } }

#guard (match Validate.validate reusedPushReference with | .error v => v.code == .v060 | _ => false)

private def publishElementRunReference : Module :=
  { publishedPushReference with funcs := publishedPushReference.funcs.map fun f => { f with blocks := f.blocks.map fun block =>
    { block with insts := block.insts.map fun
      | .def 3 (.destOpen _ ty _ count org) => .def 3 (.destOpen (.append 2) ty .elementRun count org)
      | inst => inst } } }

#guard (match Validate.validate publishElementRunReference with | .error v => v.code == .v010 | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def helperLocalExitCopy : Module :=
  let original := targeted
  let helper := { original.funcs[2] with slots := #[⟨byteTy,.mutable,0,0⟩], blocks := #[⟨[],[
    .eff (.enter 0),.def 0 (.destOpen (.slot 0) byteTy .value none (some 0)),
    .eff (.destBytes 0 [65,0] (some 0)),.def 1 (.destFinish 0 (some 0)),.eff (.destPublish 1 (some 0)),
    .def 2 (.slotAddr 0),.def 3 (.targetDest 0 0 (some 0)),.eff (.destCopy 3 2 (some 0)),
    .def 4 (.destFinish 3 (some 0)),.eff (.leave 0),.term (.escape 0 [4] [] (some 0))]⟩] }
  { original with funcs := #[original.funcs[0],original.funcs[1],helper] }

#guard (Validate.validate helperLocalExitCopy).isOk
#guard observation helperLocalExitCopy == some ([65,0,10],
  [.begin 0,.begin 1,.write 1 0,.write 1 1,.publish 1,
    .copy (.storage 1 []) 0,.write 0 0,.write 0 1,.publish 0])
#guard roundTrip helperLocalExitCopy

private def helperLocalNamedExitCopy : Module :=
  let original := helperLocalExitCopy
  let producer := { original.funcs[1] with
    slots := #[⟨byteTy,.mutable,0,0⟩], results := [⟨byteTy,.value,some 0⟩], blocks := #[
    ⟨[(0,.dest byteTy .value)],[.eff (.enter 0),.eff (.destBytes 0 [79] (some 0)),
      .def 1 (.destFinish 0 (some 0)),.eff (.destBind 0 1 (some 0)),
      .term (.invoke 2 [] [] 1 [] [⟨0,2,[]⟩] (some 0))]⟩,
    ⟨[],[.def 2 (.destNamed 0 (some 0)),.def 3 (.destAbandon 2 (some 0)),
      .eff (.destCancel 3 (some 0)),.eff (.leave 0),.term (.abort .userAbort (some 0))]⟩,
    ⟨[(4,.built byteTy .value)],[.def 5 (.destAbandonNamed 0 4 (some 0)),
      .eff (.destCancel 5 (some 0)),.def 6 (.destRelocate 4 .exitValue (some 0)),
      .eff (.leave 0),.term (.ret [6] (some 0))]⟩] }
  { original with funcs := #[original.funcs[0],producer,original.funcs[2]] }

#guard (Validate.validate helperLocalNamedExitCopy).isOk
#guard observation helperLocalNamedExitCopy == some ([65,0,10],
  [.begin 0,.write 0 0,.begin 1,.write 1 0,.write 1 1,.publish 1,.begin 2,
    .copy (.storage 2 []) 2,.write 2 0,.write 2 1,.abandon 0,.relocate 2 .exitValue,.publish 2])
#guard roundTrip helperLocalNamedExitCopy

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def stagedCall : Module :=
  let original := staged 2
  let ty := Ty.limited (.int .u8) 2
  let caller := { original.funcs[0] with blocks := #[⟨[],[
    .eff (.enter 0),.def 0 (.destOpen (.slot 0) ty .value none (some 0)),
    .def 1 (.destStage 0 (some 0)),.def 2 (.callConstruct 1 [] [1] (some 0)),
    .def 3 (.destFit 2 (some 0)),.eff (.destPublish 3 (some 0)),
    .def 4 (.slotAddr 0),.def 5 (.snapshot .owner 4),.eff (.print [.val 5] (some 0)),
    .eff (.leave 0),.term (.ret [] none)]⟩] }
  let producer := function "producer" #[⟨[(0,.dest ty .value)],[
    .eff (.destBytes 0 [65,66] (some 0)),.def 1 (.destFinish 0 (some 0)),.term (.ret [1] (some 0))]⟩]
    #[] [⟨ty,.value,none⟩]
  { original with funcs := #[caller,producer] }

#guard (Validate.validate stagedCall).isOk
#guard observation stagedCall == observation (staged 2)
#guard roundTrip stagedCall

private def stagedBranch : Module :=
  let original := staged 2
  let ty := Ty.limited (.int .u8) 2
  { original with funcs := #[{ original.funcs[0] with blocks := #[
    ⟨[],[.eff (.enter 0),.def 0 (.destOpen (.slot 0) ty .value none (some 0)),
      .def 1 (.destStage 0 (some 0)),.def 2 (.constBool true),.term (.condbr 2 1 [1] 2 [1])]⟩,
    ⟨[(3,.dest ty .value)],[.eff (.destBytes 3 [65,66] (some 0)),.def 4 (.destFinish 3 (some 0)),.term (.br 3 [4])]⟩,
    ⟨[(5,.dest ty .value)],[.eff (.destBytes 5 [67,68] (some 0)),.def 6 (.destFinish 5 (some 0)),.term (.br 3 [6])]⟩,
    ⟨[(7,.built ty .value)],[.def 8 (.destFit 7 (some 0)),.eff (.destPublish 8 (some 0)),
      .def 9 (.slotAddr 0),.def 10 (.snapshot .owner 9),.eff (.print [.val 10] (some 0)),
      .eff (.leave 0),.term (.ret [] none)]⟩] }] }

#guard (Validate.validate stagedBranch).isOk
#guard observation stagedBranch == observation (staged 2)
#guard roundTrip stagedBranch

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def unstagedFit : Module :=
  { rawBytes with funcs := rawBytes.funcs.map fun f => { f with blocks := f.blocks.map fun block =>
    { block with insts := block.insts.flatMap fun
      | .eff (.destPublish built org) => [.def 4 (.destFit built org),.eff (.destPublish 4 org)]
      | inst => [inst] } } }

#guard (match Validate.validate unstagedFit with | .error v => v.code == .v060 | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def forgedUnreachable : Module := moduleOf #[function "entry" #[⟨[],[.term .unreachable]⟩]]
#guard (match Validate.validate forgedUnreachable with | .error v => v.code == .v020 | _ => false)

private def invokeNonreturning : Module :=
  let entry := function "entry" #[
    ⟨[],[.term (.invoke 1 [] [] 1 [] [⟨0,2,[]⟩] (some 0))]⟩,
    ⟨[],[.term .unreachable]⟩,
    ⟨[],[.eff (.print [.text "caught"] (some 0)),.term (.ret [] none)]⟩]
  let helper := function "escape" #[⟨[],[.term (.escape 0 [] [] (some 0))]⟩]
  { moduleOf #[{ entry with summary := known [] [] [] false true },
      { helper with summary := known [] [0] [0] }] with targets := #[⟨0,[]⟩] }

#guard (Validate.validate invokeNonreturning).isOk
#guard observation invokeNonreturning == some ("caught\n".toUTF8.data.toList,[])
#guard roundTrip invokeNonreturning

private def returningInvokeUnreachable : Module :=
  { invokeNonreturning with funcs := invokeNonreturning.funcs.mapIdx fun index f =>
    if index == 1 then { f with blocks := #[⟨[],[.term (.ret [] none)]⟩] } else f }

#guard (match Validate.validate returningInvokeUnreachable with | .error v => v.code == .v020 | _ => false)

private def selfEscapeUnreachable : Module :=
  let original := invokeNonreturning
  { original with targets := #[⟨1,[]⟩] }

#guard (match Validate.validate selfEscapeUnreachable with | .error v => v.code == .v020 | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def emittedPushReferenceWire : String := "[\"module\",\"gir-h/0.4\",\"core-construction\",[[\"file\",\"t.goose\"]],[[\"int\",\"u8\"],[\"varr\",0],[\"grow\",1],[\"int\",\"i64\"],[\"dest\",2,\"value\"],[\"built\",2,\"value\"],[\"dest\",1,\"value\"],[\"built\",1,\"value\"],[\"view\",\"const\",0]],[],[],[],[[\"func\",\"main\",[],[],[[\"slot\",2,\"let\",0,0]],[[\"scope\",[]]],[[\"block\",[],[[\"x_enter\",0],[\"i_int\",0,3,\"0\"],[\"i_dest_open\",1,[\"dr_slot\",0],2,\"value\",[0],[0]],[\"i_dest_finish\",2,1,[0]],[\"x_dest_publish\",2,[0]],[\"i_slot\",3,0],[\"i_dest_open\",4,[\"dr_push\",3],1,\"value\",[],[0]],[\"x_dest_bytes\",4,[65],[0]],[\"i_dest_finish\",5,4,[0]],[\"i_dest_publish_ref\",6,5,[0]],[\"i_snap\",7,\"borrowed\",6],[\"i_int\",8,3,\"0\"],[\"i_elem\",9,7,8],[\"i_int\",10,0,\"66\"],[\"x_store\",9,10,[0]],[\"i_alen\",11,3],[\"i_render\",12,11,[0]],[\"i_snap\",13,\"borrowed\",6],[\"i_elem\",14,13,8],[\"i_load\",15,14],[\"i_render\",16,15,[0]],[\"x_print\",[[\"pp_val\",12],[\"pp_text\",\" \"],[\"pp_val\",16]],[0]],[\"x_leave\",0],[\"t_ret\",[],[]]]]],[\"roots\",[],[],[]],[\"summary\",[],[],[],[],[],[],[],[],1,1],[],[]]],0,[[\"origin\",0,1,\"let\"]]]\n\n"

private def emittedPushReference : Option Module := (Decode.decodeBytes emittedPushReferenceWire.toUTF8).toOption

#guard emittedPushReference.any (fun module => (Validate.validate module).isOk)
#guard emittedPushReference.any (fun module =>
  (Writer.write module).contains "[\"i_dest_publish_ref\",6,5,[0]]")

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def emittedAdaptGrowWire : String := "[\"module\",\"gir-h/0.4\",\"core-construction\",[[\"file\",\"t.goose\"]],[[\"int\",\"i64\"],[\"grow\",0],[\"dest\",1,\"value\"],[\"varr\",0],[\"dest\",3,\"value\"],[\"built\",3,\"value\"],[\"built\",1,\"value\"],[\"int\",\"u8\"],[\"view\",\"const\",7]],[],[],[],[[\"func\",\"main\",[],[],[[\"slot\",1,\"let\",0,0]],[[\"scope\",[]]],[[\"block\",[],[[\"x_enter\",0],[\"i_int\",0,0,\"1\"],[\"i_dest_open\",1,[\"dr_slot\",0],1,\"value\",[0],[0]],[\"i_dest_adapt\",2,1,3,\"value\",[0]],[\"i_call_construct\",3,1,[],[2],[0]],[\"i_dest_adapt_finish\",4,3,[0]],[\"x_dest_publish\",4,[0]],[\"i_slot\",5,0],[\"i_snap\",6,\"owner\",5],[\"i_render\",7,6,[0]],[\"x_print\",[[\"pp_val\",7]],[0]],[\"x_leave\",0],[\"t_ret\",[],[]]]]],[\"roots\",[],[],[]],[\"summary\",[],[],[],[],[],[],[],[],0,1],[],[]],[\"func\",\"make\",[],[[\"result\",3,\"value\",[]]],[],[[\"scope\",[]]],[[\"block\",[[\"bp\",0,4]],[[\"x_enter\",0],[\"i_int\",1,0,\"7\"],[\"x_dest_write\",0,1,[0]],[\"i_dest_finish\",2,0,[0]],[\"x_leave\",0],[\"t_ret\",[2],[0]]]]],[\"roots\",[],[],[[]]],[\"summary\",[],[],[],[],[],[0],[],[],0,0],[],[]]],0,[[\"origin\",0,1,\"let\"]]]\n\n"

private def emittedAdaptGrow : Option Module := (Decode.decodeBytes emittedAdaptGrowWire.toUTF8).toOption

#guard emittedAdaptGrow.any (fun module => (Validate.validate module).isOk)
#guard emittedAdaptGrow.any (fun module =>
  (Writer.write module).contains "[\"i_dest_adapt\",2,1,3,\"value\",[0]]" &&
  (Writer.write module).contains "[\"i_dest_adapt_finish\",4,3,[0]]")

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def emittedAdaptVarrWire : String := "[\"module\",\"gir-h/0.4\",\"core-construction\",[[\"file\",\"t.goose\"]],[[\"int\",\"i64\"],[\"varr\",0],[\"dest\",1,\"value\"],[\"grow\",0],[\"dest\",3,\"value\"],[\"built\",3,\"value\"],[\"built\",1,\"value\"],[\"int\",\"u8\"],[\"view\",\"const\",7]],[],[],[],[[\"func\",\"main\",[],[],[[\"slot\",1,\"let\",0,0]],[[\"scope\",[]]],[[\"block\",[],[[\"x_enter\",0],[\"i_int\",0,0,\"1\"],[\"i_dest_open\",1,[\"dr_slot\",0],1,\"value\",[0],[0]],[\"i_dest_adapt\",2,1,3,\"value\",[0]],[\"i_call_construct\",3,1,[],[2],[0]],[\"i_dest_adapt_finish\",4,3,[0]],[\"x_dest_publish\",4,[0]],[\"i_slot\",5,0],[\"i_snap\",6,\"owner\",5],[\"i_render\",7,6,[0]],[\"x_print\",[[\"pp_val\",7]],[0]],[\"x_leave\",0],[\"t_ret\",[],[]]]]],[\"roots\",[],[],[]],[\"summary\",[],[],[],[],[],[],[],[],0,1],[],[]],[\"func\",\"make\",[],[[\"result\",3,\"value\",[]]],[],[[\"scope\",[]]],[[\"block\",[[\"bp\",0,4]],[[\"x_enter\",0],[\"i_int\",1,0,\"7\"],[\"x_dest_write\",0,1,[0]],[\"i_dest_finish\",2,0,[0]],[\"x_leave\",0],[\"t_ret\",[2],[0]]]]],[\"roots\",[],[],[[]]],[\"summary\",[],[],[],[],[],[0],[],[],0,0],[],[]]],0,[[\"origin\",0,1,\"let\"]]]\n\n"

private def emittedAdaptVarr : Option Module := (Decode.decodeBytes emittedAdaptVarrWire.toUTF8).toOption

#guard emittedAdaptVarr.any (fun module => (Validate.validate module).isOk)
#guard emittedAdaptVarr.any (fun module =>
  (Writer.write module).contains "[\"i_dest_adapt\",2,1,3,\"value\",[0]]" &&
  (Writer.write module).contains "[\"i_dest_adapt_finish\",4,3,[0]]")

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

#guard emittedPushReference.bind observation == some ("1 66\n".toUTF8.data.toList,
  [.begin 0,.publish 0,.begin 1,.write 1 0,.publish 1])
#guard emittedPushReference.any roundTrip
#guard emittedAdaptGrow.bind observation == some ("[7]\n".toUTF8.data.toList,
  [.begin 0,.write 0 0,.relocate 0 .headerRemoval,.publish 0])
#guard emittedAdaptGrow.any roundTrip
#guard emittedAdaptVarr.bind observation == some ("[7]\n".toUTF8.data.toList,
  [.begin 0,.write 0 0,.publish 0])
#guard emittedAdaptVarr.any roundTrip

private def unfinishedAdaptation : Module :=
  let original := emittedAdaptGrow.getD rawBytes
  { original with funcs := original.funcs.mapIdx fun index f =>
    if index == 0 then { f with blocks := f.blocks.map fun block =>
      { block with insts := block.insts.map fun
        | .def 4 (.destAdaptFinish ..) => .def 4 .constUnit
        | .eff (.destPublish _ org) => .eff (.destPublish 3 org)
        | inst => inst } } else f }

#guard (match Validate.validate unfinishedAdaptation with | .error v => v.code == .v060 | _ => false)

private def nestedAdaptation : Module :=
  let original := emittedAdaptGrow.getD rawBytes
  { original with funcs := original.funcs.mapIdx fun index f =>
    if index == 0 then { f with blocks := f.blocks.map fun block =>
      { block with insts := block.insts.flatMap fun
        | .def 3 (.callConstruct callee args _ org) =>
            [.def 8 (.destAdapt 2 (.varr (.int .i64)) .value org),.def 3 (.callConstruct callee args [8] org)]
        | inst => [inst] } } else f }

#guard (match Validate.validate nestedAdaptation with | .error v => v.code == .v060 | _ => false)

private def missingAdaptationLineage : Module :=
  let original := rawBytes
  { original with funcs := original.funcs.map fun f => { f with blocks := f.blocks.map fun block =>
    { block with insts := block.insts.map fun
      | .def 1 (.destFinish _ org) => .def 1 (.destAdaptFinish 0 org)
      | inst => inst } } }

#guard (match Validate.validate missingAdaptationLineage with | .error v => v.code == .v010 | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def nonemptyAdaptation : Module :=
  let original := emittedAdaptGrow.getD rawBytes
  { original with funcs := original.funcs.mapIdx fun index f =>
    if index == 0 then { f with blocks := f.blocks.map fun block =>
      { block with insts := block.insts.flatMap fun
        | .def 2 op => [.eff (.destWrite 1 0 (some 0)),.def 2 op]
        | inst => [inst] } } else f }

#guard (match Validate.validate nonemptyAdaptation with | .error v => v.code == .v060 | _ => false)

private def cancelledAdaptation : Module :=
  let owner := Ty.grow (.int .i64)
  moduleOf #[function "entry" #[⟨[],[
    .eff (.enter 0),.def 0 (.destOpen (.slot 0) owner .value none (some 0)),
    .def 1 (.destAdapt 0 (.varr (.int .i64)) .value (some 0)),
    .def 2 (.destAbandon 1 (some 0)),.def 3 (.destAdaptFinish 2 (some 0)),
    .eff (.destCancel 3 (some 0)),.eff (.leave 0),.term (.ret [] none)]⟩] #[⟨owner,.mutable,0,0⟩]]

#guard (Validate.validate cancelledAdaptation).isOk
#guard observation cancelledAdaptation == some ([],[.begin 0,.abandon 0])
#guard roundTrip cancelledAdaptation

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def stagedAdaptation (capacity : Nat) : Module :=
  let owner := Ty.limited (.int .u8) capacity
  moduleOf #[function "entry" #[⟨[],[
    .eff (.enter 0),.def 0 (.destOpen (.slot 0) owner .value none (some 0)),
    .def 1 (.destStage 0 (some 0)),.def 2 (.destAdapt 1 byteTy .value (some 0)),
    .eff (.destBytes 2 [65,66] (some 0)),.def 3 (.destFinish 2 (some 0)),
    .def 4 (.destAdaptFinish 3 (some 0)),.def 5 (.destFit 4 (some 0)),
    .eff (.destPublish 5 (some 0)),.def 6 (.slotAddr 0),.def 7 (.snapshot .owner 6),
    .eff (.print [.val 7] (some 0)),.eff (.leave 0),.term (.ret [] none)]⟩] #[⟨owner,.mutable,0,0⟩]]

#guard (Validate.validate (stagedAdaptation 2)).isOk
#guard observation (stagedAdaptation 2) == some ([65,66,10],
  [.begin 0,.stage 0,.write 0 0,.write 0 1,.relocate 0 .headerRemoval,.copy (.storage 1 []) 0,.publish 0])
#guard roundTrip (stagedAdaptation 2)
#guard (match Run.run 1000 .release (stagedAdaptation 1) with
  | .done (.aborted .capacity 0) stdout events => stdout.isEmpty &&
      events == [.begin 0,.stage 0,.write 0 0,.write 0 1,.relocate 0 .headerRemoval]
  | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def adaptedNamedProducer : Module :=
  let owner := Ty.varr (.int .i64)
  let producer := Ty.grow (.int .i64)
  let caller := function "entry" #[⟨[],[
    .eff (.enter 0),.def 0 (.destOpen (.slot 0) owner .value none (some 0)),
    .def 1 (.destAdapt 0 producer .value (some 0)),.def 2 (.callConstruct 1 [] [1] (some 0)),
    .def 3 (.destAdaptFinish 2 (some 0)),.eff (.destPublish 3 (some 0)),
    .def 4 (.slotAddr 0),.def 5 (.snapshot .owner 4),.def 6 (.render 5 (some 0)),
    .eff (.print [.val 6] (some 0)),.eff (.leave 0),.term (.ret [] none)]⟩]
    #[⟨owner,.mutable,0,0⟩]
  let callee := function "make" #[⟨[(0,.dest producer .value)],[
      .eff (.enter 0),.def 1 (.constInt .i64 7),.eff (.destWrite 0 1 (some 0)),
      .def 2 (.destFinish 0 (some 0)),.eff (.destBind 0 2 (some 0)),
      .def 3 (.slotAddr 0),.def 4 (.snapshot .owner 3),.def 5 (.constInt .i64 0),
      .def 6 (.indexChecked 4 5 (some 0)),.def 7 (.constInt .i64 9),.eff (.store 6 7 (some 0)),
      .def 8 (.snapshot .owner 3),.eff (.print [.val 8] (some 0)),.def 9 (.destNamed 0 (some 0)),
      .eff (.leave 0),.term (.ret [9] (some 0))]⟩]
    #[⟨producer,.mutable,0,0⟩] [⟨producer,.value,some 0⟩]
  moduleOf #[caller,callee]

#guard (Validate.validate adaptedNamedProducer).isOk
#guard observation adaptedNamedProducer == some ("[9]\n[9]\n".toUTF8.data.toList,
  [.begin 0,.write 0 0,.publish 0])
#guard roundTrip adaptedNamedProducer

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def abortBeforeAdaptationFinish : Module :=
  let original := emittedAdaptGrow.getD rawBytes
  { original with funcs := original.funcs.mapIdx fun index f =>
    if index == 0 then { f with
      summary := known [] [] [] true false, blocks := f.blocks.map fun block => { block with insts := block.insts.take 5 ++ [.term (.abort .userAbort (some 0))] } } else f }

#guard (Validate.validate abortBeforeAdaptationFinish).isOk
#guard (match Run.run 1000 .release abortBeforeAdaptationFinish with
  | .done (.aborted .userAbort 0) stdout events => stdout.isEmpty && events == [.begin 0,.write 0 0]
  | _ => false)

end Goose.Construct.GIR.Checks

namespace Goose.Construct.GIR.Checks

private def adaptedKnownCount (bytes : List UInt8) : Module :=
  let owner := Ty.grow (.int .u8)
  moduleOf #[function "entry" #[⟨[],[
    .eff (.enter 0),.def 0 (.constInt .i64 1),
    .def 1 (.destOpen (.slot 0) owner .value (some 0) (some 0)),
    .def 2 (.destAdapt 1 byteTy .value (some 0)),.eff (.destBytes 2 bytes (some 0)),
    .def 3 (.destFinish 2 (some 0)),.def 4 (.destAdaptFinish 3 (some 0)),
    .eff (.destPublish 4 (some 0)),.eff (.leave 0),.term (.ret [] none)]⟩]
    #[⟨owner,.mutable,0,0⟩]]

#guard (match Validate.validate (adaptedKnownCount [65,66]) with
  | .error error => error.code == .v060
  | _ => false)
#guard (Validate.validate (adaptedKnownCount [65])).isOk

private def invokeReadOnlyForward : Module :=
  let ty := Ty.arr (.int .u8) 1
  let entry := function "entry" #[
    ⟨[],[
      .eff (.enter 0),.def 0 (.constInt .u8 65),.def 1 (.arrLit ty [0]),
      .eff (.slotInit 0 1 (some 0)),.def 2 (.slotAddr 0),.def 3 (.refFreeze 2),
      .term (.invoke 1 [] [] 1 [3] [] (some 0))]⟩,
    ⟨[(4,.data (.ref .readOnly ty))],[
      .def 5 (.snapshot .borrowed 4),.def 6 (.constInt .i64 0),.def 7 (.indexChecked 5 6 (some 0)),
      .def 8 (.constInt .u8 66),.eff (.store 7 8 (some 0)),.eff (.leave 0),.term (.ret [] none)]⟩]
    #[⟨ty,.immutable,0,0⟩]
  let callee := function "callee" #[⟨[],[.term (.ret [] none)]⟩]
  moduleOf #[entry,callee]

#guard (match Validate.validate invokeReadOnlyForward with
  | .error error => error.code == .v030
  | _ => false)

private def invokeWritableForward : Module :=
  let ty := Ty.arr (.int .u8) 1
  let entry := function "entry" #[
    ⟨[],[
      .eff (.enter 0),.def 0 (.constInt .u8 65),.def 1 (.arrLit ty [0]),
      .eff (.slotInit 0 1 (some 0)),.def 2 (.slotAddr 0),.term (.invoke 1 [] [] 1 [2] [] (some 0))]⟩,
    ⟨[(3,.data (.ref .mutable ty))],[
      .def 4 (.snapshot .borrowed 3),.def 5 (.constInt .i64 0),.def 6 (.indexChecked 4 5 (some 0)),
      .def 7 (.constInt .u8 66),.eff (.store 6 7 (some 0)),
      .eff (.print [.val 4] (some 0)),.eff (.leave 0),.term (.ret [] none)]⟩]
    #[⟨ty,.mutable,0,0⟩]
  let callee := function "callee" #[⟨[],[.term (.ret [] none)]⟩]
  moduleOf #[entry,callee]

#guard (Validate.validate invokeWritableForward).isOk
#guard observation invokeWritableForward == some ([66,10],[])

private def invokeImmutableArrayContents : Module :=
  let ty := Ty.arr (.int .u8) 1
  let entry := function "entry" #[
    ⟨[],[
      .eff (.enter 0),.def 0 (.constInt .u8 65),.def 1 (.arrLit ty [0]),
      .eff (.slotInit 0 1 (some 0)),.def 2 (.slotAddr 0),.term (.br 1 [2])]⟩,
    ⟨[(3,.data (.ref .readOnly ty))],[.term (.invoke 1 [] [] 2 [3] [] (some 0))]⟩,
    ⟨[(4,.data (.ref .readOnly ty))],[
      .def 5 (.snapshot .borrowed 4),.def 6 (.constInt .i64 0),.def 7 (.indexChecked 5 6 (some 0)),
      .def 8 (.constInt .u8 66),.eff (.store 7 8 (some 0)),.eff (.print [.val 5] (some 0)),
      .eff (.leave 0),.term (.ret [] none)]⟩]
    #[⟨ty,.immutable,0,0⟩]
  let callee := function "callee" #[⟨[],[.term (.ret [] none)]⟩]
  moduleOf #[entry,callee]

#guard (Validate.validate invokeImmutableArrayContents).isOk
#guard observation invokeImmutableArrayContents == some ([66,10],[])

private def publishCalledLocalRef : Module :=
  let byteTy := Ty.varr (.int .u8)
  let ownerTy := Ty.grow byteTy
  let entry := function "entry" #[⟨[],[
    .def 0 (.call 1 [] (some 0)),.def 1 (.snapshot .borrowed 0),
    .eff (.print [.val 1] (some 0)),.term (.ret [] none)]⟩]
  let maker := function "maker" #[⟨[],[
    .eff (.enter 0),.def 0 (.constInt .i64 0),
    .def 1 (.destOpen (.slot 0) ownerTy .value (some 0) (some 0)),
    .def 2 (.destFinish 1 (some 0)),.eff (.destPublish 2 (some 0)),.def 3 (.slotAddr 0),
    .def 4 (.destOpen (.push 3) byteTy .value none (some 0)),
    .def 5 (.callConstruct 2 [] [4] (some 0)),.def 6 (.destPublishRef 5 (some 0)),
    .eff (.leave 0),.term (.ret [6] (some 0))]⟩]
    #[⟨ownerTy,.mutable,0,0⟩] [⟨.ref .mutable byteTy,.register,none⟩]
  let producer := function "producer" #[⟨[(0,.dest byteTy .value)],[
    .eff (.destBytes 0 [65] (some 0)),.def 1 (.destFinish 0 (some 0)),.term (.ret [1] (some 0))]⟩]
    #[] [⟨byteTy,.value,none⟩]
  moduleOf #[entry,maker,producer]

#guard (match Validate.validate publishCalledLocalRef with
  | .error error => error.code == .v040
  | _ => false)

private def invokePublishesLocalRef : Module :=
  let byteTy := Ty.varr (.int .u8)
  let ownerTy := Ty.grow byteTy
  let entry := function "entry" #[⟨[],[
    .def 0 (.call 1 [] (some 0)),.def 1 (.snapshot .borrowed 0),
    .eff (.print [.val 1] (some 0)),.term (.ret [] (some 0))]⟩]
  let caller := function "caller" #[
    ⟨[],[
      .eff (.enter 0),.def 0 (.constInt .i64 0),
      .def 1 (.destOpen (.slot 0) ownerTy .value (some 0) (some 0)),
      .def 2 (.destFinish 1 (some 0)),.eff (.destPublish 2 (some 0)),.def 3 (.slotAddr 0),
      .def 4 (.destOpen (.push 3) byteTy .value none (some 0)),
      .term (.invoke 2 [] [4] 1 [] [] (some 0))]⟩,
    ⟨[(5,.data (.int .i64)),(6,.built byteTy .value)],[
      .def 7 (.destPublishRef 6 (some 0)),.eff (.leave 0),.term (.ret [7] (some 0))]⟩]
    #[⟨ownerTy,.mutable,0,0⟩] [⟨.ref .mutable byteTy,.register,none⟩]
  let producer := function "producer" #[⟨[(0,.dest byteTy .value)],[
    .def 1 (.constInt .i64 1),.eff (.destBytes 0 [65] (some 0)),
    .def 2 (.destFinish 0 (some 0)),.term (.ret [1,2] (some 0))]⟩]
    #[] [⟨.int .i64,.register,none⟩,⟨byteTy,.value,none⟩]
  moduleOf #[entry,caller,producer]

#guard (match Validate.validate invokePublishesLocalRef with
  | .error error => error.code == .v040
  | _ => false)

end Goose.Construct.GIR.Checks
