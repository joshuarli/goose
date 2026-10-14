import Goose.Construct.Eval

namespace Goose.Construct.ExecutionChecks
open Goose.Core (ConstructionEvent AbortKind)

private def localVar (name : String) (ty : Ty) (scope : Nat := 0) : LocalVar :=
  ⟨name, ty, .mutable, scope, 0⟩

private def implementation (name : String) (vars : Array LocalVar) (body : Block)
    (results : Array ResultDescriptor := #[]) (params : Array Param := #[]) : Impl :=
  ⟨name, params, results, vars, body, .unknown⟩

private def moduleOf (implementations : Array Impl) (targets : Array Goose.Core.NonlocalTarget := #[]) : Module :=
  ⟨#["execution.goose"], #[], #[], implementations,
    implementations.mapIdx (fun index _ => ⟨index, "", [], [], []⟩), 0,
    #[⟨0, 17, "execution"⟩], #[], targets⟩

def observes (module : Module) : Option (List UInt8 × List ConstructionEvent) :=
  match eval 1000 .release module with
  | .done .returned stdout events => some (stdout.data.toList, events)
  | _ => none

private def rawBytes : Module := moduleOf #[implementation "entry"
  #[localVar "bytes" (.varr (.int .u8))]
  (.mk 0 [.letS 0 (.bytes (.varr (.int .u8)) [65, 0, 255] 0) 0,
    .print [.view (.of (.var 0))] 0] none)]

#guard observes rawBytes == some ([65, 0, 255, 10],
    [.begin 0, .write 0 0, .write 0 1, .write 0 2, .publish 0]) 

private def nested : Module := moduleOf #[implementation "entry"
  #[localVar "nested" (.varr (.varr (.int .u8)))]
  (.mk 0 [.letS 0 (.arrLit (.varr (.varr (.int .u8)))
      [.bytes (.varr (.int .u8)) [65, 0] 0, .bytes (.varr (.int .u8)) [255] 0]) 0,
    .print [.view (.of (.elem (.of (.var 0)) (.lit .i64 0) 0)),
      .view (.of (.elem (.of (.var 0)) (.lit .i64 1) 0))] 0] none)]

#guard observes nested == some ([65, 0, 255, 10],
    [.begin 0, .begin 1, .write 1 0, .write 1 1, .write 0 0,
      .begin 2, .write 2 0, .write 0 1, .publish 0]) 

private def multiple : Module := moduleOf #[
  implementation "entry" #[localVar "scalar" (.int .i64), localVar "bytes" (.varr (.int .u8))]
    (.mk 0 [.receive [0, 1] (.call 1 [] 0) 0,
      .print [.expr (.read (.var 0)), .view (.of (.var 1))] 0] none),
  implementation "producer" #[] (.mk 0 [] (some (.values [.lit .i64 7, .bytes (.varr (.int .u8)) [65] 0])))
    #[⟨.int .i64, .register, none⟩, ⟨.varr (.int .u8), .value, none⟩]]

#guard observes multiple == some ([55, 65, 10], [.begin 0, .write 0 0, .publish 0]) 

private def abortPrefix : Module := moduleOf #[implementation "entry"
  #[localVar "bytes" (.varr (.int .u8))]
  (.mk 0 [.print [.text "before"] 0,
    .letS 0 (.arrLit (.varr (.int .u8)) [.lit .u8 65,
      .blockE (.mk 1 [.abort "stop" 0] (some (.lit .u8 66)))]) 0] none)]

#guard (match eval 1000 .release abortPrefix with
  | .done (.aborted .userAbort 0) stdout events =>
      stdout.data.toList == [98, 101, 102, 111, 114, 101, 10] &&
      events == [.begin 0, .write 0 0]
  | _ => false) 

private def appendProducer : Module := moduleOf #[
  implementation "entry" #[localVar "owner" (.grow (.int .u8))]
    (.mk 0 [.letS 0 (.arrLit (.grow (.int .u8)) [.lit .u8 65]) 0,
      .appendConstruct (.var 0) (.call 1 [] 0) 0,
      .print [.view (.of (.var 0))] 0] none),
  implementation "producer" #[] (.mk 0 [] (some (.bytes (.varr (.int .u8)) [66, 67] 0)))
    #[⟨.varr (.int .u8), .value, none⟩]]

#guard observes appendProducer == some ([65, 66, 67, 10],
  [.begin 0, .write 0 0, .publish 0, .begin 1, .write 1 0, .write 1 1, .publish 1]) 

private def named : Module := moduleOf #[
  implementation "entry" #[localVar "result" (.varr (.int .u8))]
    (.mk 0 [.letS 0 (.call 1 [] 0) 0, .print [.view (.of (.var 0))] 0] none),
  implementation "named" #[localVar "result" (.grow (.int .u8))]
    (.mk 0 [.letS 0 (.arrLit (.grow (.int .u8)) [.lit .u8 65]) 0,
      .expr (.push (.var 0) (.lit .u8 66) (some 0)) 0]
      (some (.resultLocal 0 0)))
    #[⟨.varr (.int .u8), .value, some 0⟩]]

#guard observes named == some ([65, 66, 10],
  [.begin 0, .write 0 0, .begin 1, .write 1 0, .publish 1, .publish 0])

private def namedAlternate : Module := moduleOf #[
  implementation "entry" #[localVar "result" (.varr (.int .u8))]
    (.mk 0 [.letS 0 (.call 1 [] 0) 0, .print [.view (.of (.var 0))] 0] none),
  implementation "alternate" #[localVar "result" (.varr (.int .u8))]
    (.mk 0 [.letS 0 (.bytes (.varr (.int .u8)) [65] 0) 0,
      .retValues [.bytes (.varr (.int .u8)) [66] 0] 0] none)
    #[⟨.varr (.int .u8), .value, some 0⟩]]

#guard observes namedAlternate == some ([66, 10],
  [.begin 0, .write 0 0, .begin 1, .write 1 0, .abandon 0,
    .relocate 1 .exitValue, .publish 1])

private def staged : Module := moduleOf #[
  implementation "entry" #[localVar "owner" (.limited (.int .u8) 3)]
    (.mk 0 [.letS 0 (.arrLit (.limited (.int .u8) 3) [.lit .u8 65]) 0,
      .appendConstruct (.var 0) (.call 1 [] 0) 0,
      .print [.view (.of (.var 0))] 0] none),
  implementation "producer" #[] (.mk 0 [.print [.text "effect"] 0]
      (some (.bytes (.varr (.int .u8)) [66, 67] 0)))
    #[⟨.varr (.int .u8), .value, none⟩]]

#guard observes staged == some ([101, 102, 102, 101, 99, 116, 10, 65, 66, 67, 10],
  [.begin 0, .write 0 0, .publish 0, .begin 1, .stage 1,
    .write 1 0, .write 1 1, .copy (.storage 1 []) 1, .publish 1])

private def shrinkThenPush : Module := moduleOf #[implementation "entry"
  #[localVar "owner" (.limited (.int .u8) 3)]
  (.mk 0 [.letS 0 (.bytes (.limited (.int .u8) 3) [65, 66, 67] 0) 0,
    .popN (.var 0) (.lit .i64 2) 0,
    .expr (.push (.var 0) (.lit .u8 68) (some 0)) 0,
    .print [.view (.of (.var 0))] 0] none)]

#guard (observes shrinkThenPush).map Prod.fst == some [65, 68, 10]

private def breakConstruction : Module := moduleOf #[implementation "entry"
  #[localVar "result" (.varr (.int .u8))]
  (.mk 0 [.letS 0 (.blockE (.mk 1 [] (some (.arrLit (.varr (.int .u8))
      [.lit .u8 65, .ifE (.bool true) (.mk 2 [.breakValue (.bytes (.varr (.int .u8)) [66] 0) 0] none) (.mk 3 [] (some (.lit .u8 67)))])))) 0,
    .print [.view (.of (.var 0))] 0] none)]

#guard observes breakConstruction == some ([66, 10],
  [.begin 0, .write 0 0, .begin 1, .write 1 0, .abandon 0,
    .relocate 1 .exitValue, .publish 1])

private def nonlocal : Module := moduleOf #[
  implementation "entry" #[localVar "result" (.varr (.int .u8))]
    (.mk 0 [.letS 0 (.call 1 [] 0) 0, .print [.view (.of (.var 0))] 0] none),
  implementation "catcher" #[] (.mk 0 [] (some (.arrLit (.varr (.int .u8))
    [.lit .u8 65, .call 2 [] 0]))) #[⟨.varr (.int .u8), .value, none⟩],
  implementation "escape" #[] (.mk 0 [.print [.text "escape"] 0,
    .returnFrom 0 [.bytes (.varr (.int .u8)) [66] 0] 0] (some (.lit .u8 67)))
    #[⟨.int .u8, .register, none⟩]] #[⟨1, []⟩]

#guard observes nonlocal == some ([101, 115, 99, 97, 112, 101, 10, 66, 10],
  [.begin 0, .write 0 0, .begin 1, .write 1 0, .abandon 0,
    .relocate 1 .exitValue, .publish 1])

private def parameter : Module := moduleOf #[
  implementation "entry" #[localVar "scalar" (.int .i64)]
    (.mk 0 [.letS 0 (.lit .i64 7) 0,
      .expr (.call 1 [.byVal (.read (.var 0)), .construct (.bytes (.varr (.int .u8)) [65] 0)] 0) 0] none),
  implementation "parameters" #[localVar "bytes" (.varr (.int .u8)), localVar "scalar" (.int .i64)]
    (.mk 0 [.print [.expr (.read (.var 1)), .view (.of (.var 0))] 0] none)
    #[] #[⟨1, .byValue⟩, ⟨0, .byValue⟩]]

#guard observes parameter == some ([55, 65, 10], [.begin 0, .write 0 0, .publish 0])

private def whole : Module := moduleOf #[implementation "entry"
  #[localVar "owner" (.growshrink (.int .u8))]
  (.mk 0 [.letS 0 (.bytes (.growshrink (.int .u8)) [65, 66] 0) 0,
    .assignWhole (.var 0) (.bytes (.varr (.int .u8)) [67] 0) 0,
    .print [.view (.of (.var 0))] 0] none)]

#guard (observes whole).map Prod.fst == some [67, 10]

private def dynamicEach : Module := moduleOf #[implementation "entry"
  #[localVar "owner" (.grow (.int .u8)), localVar "element" (.int .u8) 1]
  (.mk 0 [.letS 0 (.bytes (.grow (.int .u8)) [65] 0) 0,
    .forEach 1 none (.of (.var 0)) false (.mk 1
      [.ifS (.cmp .eq (.read (.var 1)) (.lit .u8 65))
        (.mk 2 [.expr (.push (.var 0) (.lit .u8 66) (some 0)) 0] none) none 0,
       .print [.expr (.read (.var 1))] 0] none) 0] none)]

#guard (observes dynamicEach).map Prod.fst == some [54, 53, 10, 54, 54, 10]

private def nestedEscape : Module := moduleOf #[
  implementation "entry" #[localVar "result" (.varr (.varr (.int .u8)))]
    (.mk 0 [.letS 0 (.call 1 [] 0) 0,
      .print [.view (.of (.elem (.of (.var 0)) (.lit .i64 0) 0))] 0] none),
  implementation "catcher" #[] (.mk 0 [] (some (.arrLit (.varr (.varr (.int .u8)))
    [.bytes (.varr (.int .u8)) [65] 0,
      .arrLit (.varr (.int .u8)) [.lit .u8 66, .call 2 [] 0]])))
    #[⟨.varr (.varr (.int .u8)), .value, none⟩],
  implementation "escape" #[] (.mk 0 [.returnFrom 0
    [.arrLit (.varr (.varr (.int .u8))) [.bytes (.varr (.int .u8)) [67] 0]] 0] (some (.lit .u8 68)))
    #[⟨.int .u8, .register, none⟩]] #[⟨1, []⟩]

#guard observes nestedEscape == some ([67, 10],
  [.begin 0, .begin 1, .write 1 0, .write 0 0, .begin 2, .write 2 0,
    .begin 3, .begin 4, .write 4 0, .write 3 0,
    .abandon 2, .abandon 0, .relocate 3 .exitValue, .publish 3])

private def recursion : Module := moduleOf #[
  implementation "entry" #[localVar "result" (.int .i64)]
    (.mk 0 [.letS 0 (.call 1 [.byVal (.lit .i64 0)] 0) 0,
      .print [.expr (.read (.var 0))] 0] none),
  implementation "descend" #[localVar "depth" (.int .i64), localVar "child" (.int .i64) 1]
    (.mk 0 [.ifS (.cmp .eq (.read (.var 0)) (.lit .i64 0))
      (.mk 1 [.letS 1 (.call 1 [.byVal (.lit .i64 1)] 0) 0,
        .retValues [.bin .add (.read (.var 1)) (.lit .i64 100) 0] 0] none)
      (some (.mk 2 [.expr (.call 2 [] 0) 0] none)) 0] (some (.lit .i64 999)))
    #[⟨.int .i64, .register, none⟩] #[⟨0, .byValue⟩],
  implementation "escape" #[] (.mk 0 [.returnFrom 0 [.lit .i64 7] 0] none)] #[⟨1, []⟩]

#guard (observes recursion).map Prod.fst == some [49, 48, 55, 10]

private def copyAndFill : Module := moduleOf #[implementation "entry"
  #[localVar "source" (.varr (.int .u8)), localVar "copy" (.varr (.int .u8)),
    localVar "fill" (.arr (.varr (.int .u8)) 2)]
  (.mk 0 [.letS 0 (.bytes (.varr (.int .u8)) [65] 0) 0,
    .letS 1 (.copy (.varr (.int .u8)) (.var 0) 0) 0,
    .letS 2 (.fill (.arr (.varr (.int .u8)) 2)
      (.blockE (.mk 1 [.print [.text "once"] 0]
        (some (.bytes (.varr (.int .u8)) [66] 0))))) 0,
    .print [.view (.of (.var 1)),
      .view (.of (.elem (.of (.var 2)) (.lit .i64 0) 0)),
      .view (.of (.elem (.of (.var 2)) (.lit .i64 1) 0))] 0] none)]

#guard (observes copyAndFill).map Prod.fst == some [111, 110, 99, 101, 10, 65, 66, 66, 10]

private def timeoutLoop : Module := moduleOf #[implementation "entry" #[]
  (.mk 0 [.print [.text "before"] 0,
    .while (.bool true) (.mk 1 [] none) 0] none)]

#guard match eval 30 .release timeoutLoop with
  | .timeout stdout events => stdout.data.toList == [98, 101, 102, 111, 114, 101, 10] && events.isEmpty
  | _ => false

private def namedHeaderRemoval : Module := moduleOf #[
  implementation "entry" #[localVar "result" (.grow (.int .u8))]
    (.mk 0 [.letS 0 (.call 1 [] 0) 0, .print [.view (.of (.var 0))] 0] none),
  implementation "named" #[localVar "result" (.varr (.int .u8))]
    (.mk 0 [.letS 0 (.bytes (.varr (.int .u8)) [65, 66] 0) 0]
      (some (.resultLocal 0 0)))
    #[⟨.varr (.int .u8), .value, some 0⟩]]

#guard observes namedHeaderRemoval == some ([65, 66, 10],
  [.begin 0, .write 0 0, .write 0 1, .relocate 0 .headerRemoval, .publish 0])

private def elementRunLocal : Module := moduleOf #[
  implementation "entry" #[localVar "owner" (.grow (.int .u8))]
    (.mk 0 [.letS 0 (.bytes (.grow (.int .u8)) [65] 0) 0,
      .appendConstruct (.var 0) (.call 1 [] 0) 0,
      .print [.view (.of (.var 0))] 0] none),
  implementation "local" #[localVar "result" (.varr (.int .u8))]
    (.mk 0 [.letS 0 (.bytes (.varr (.int .u8)) [66] 0) 0]
      (some (.resultLocal 0 0)))
    #[⟨.varr (.int .u8), .elementRun, none⟩]]

#guard observes elementRunLocal == some ([65, 66, 10],
  [.begin 0, .write 0 0, .publish 0, .begin 1, .begin 2, .write 2 0, .publish 2,
    .copy (.storage 1 []) 1, .write 1 0, .publish 1])

private def staticSlice : Module := moduleOf #[
  implementation "entry" #[localVar "slice" (.slice .readOnly (.int .u8))]
    (.mk 0 [.letS 0 (.call 1 [] 0) 0, .print [.expr (.read (.var 0))] 0] none),
  implementation "static" #[] (.mk 0 [] (some (.bytes (.slice .readOnly (.int .u8)) [65, 0, 255] 0)))
    #[⟨.slice .readOnly (.int .u8), .register, none⟩]]

#guard observes staticSlice == some ([65, 0, 255, 10], [])

private def structural : Module := moduleOf #[implementation "entry"
  #[localVar "array" (.arr (.int .i64) 2), localVar "nested" (.varr (.varr (.int .u8)))]
  (.mk 0 [.letS 0 (.arrLit (.arr (.int .i64) 2) [.lit .i64 1, .lit .i64 2]) 0,
    .letS 1 (.arrLit (.varr (.varr (.int .u8)))
      [.bytes (.varr (.int .u8)) [34, 92, 10, 0, 255] 0]) 0,
    .print [.expr (.ref .readOnly (.var 0)), .text " ", .view (.of (.var 1))] 0] none)]

#guard (observes structural).map Prod.fst == some
  [91, 49, 44, 32, 50, 93, 32, 91, 34, 92, 34, 92, 92, 92, 110, 0, 255, 34, 93, 10]

private def stringPrefix : Module := moduleOf #[implementation "entry"
  #[localVar "string" (.varr (.int .u8))]
  (.mk 0 [.letS 0 (.str (.varr (.int .u8))
    [.text "A", .expr (.blockE (.mk 1 [.abort "stop" 0] (some (.lit .i64 7))))] 0) 0] none)]

#guard match eval 1000 .release stringPrefix with
  | .done (.aborted .userAbort 0) stdout events => stdout.isEmpty && events == [.begin 0, .write 0 0]
  | _ => false

private def printSnapshot : Module := moduleOf #[implementation "entry"
  #[localVar "owner" (.growshrink (.int .u8))]
  (.mk 0 [.letS 0 (.bytes (.growshrink (.int .u8)) [65] 0) 0,
    .print [.view (.of (.var 0)), .expr (.blockE (.mk 1
      [.print [.text "inner"] 0, .clear (.var 0) 0] (some (.lit .i64 7))))] 0] none)]

#guard (observes printSnapshot).map Prod.fst == some [105, 110, 110, 101, 114, 10, 65, 55, 10]

private def nestedWrite : Module := moduleOf #[implementation "entry"
  #[localVar "nested" (.varr (.varr (.int .u8)))]
  (.mk 0 [.letS 0 (.arrLit (.varr (.varr (.int .u8))) [.bytes (.varr (.int .u8)) [65] 0]) 0,
    .assign (.elem (.of (.elem (.of (.var 0)) (.lit .i64 0) 0)) (.lit .i64 0) 0) (.lit .u8 66) 0,
    .print [.view (.of (.elem (.of (.var 0)) (.lit .i64 0) 0))] 0] none)]

#guard (observes nestedWrite).map Prod.fst == some [66, 10]

end Goose.Construct.ExecutionChecks
