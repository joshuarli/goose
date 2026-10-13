import Goose.Lower.Commands

namespace Goose.GIR.ShrinkChecks

open Goose.Core

private def growTy : Ty := .growshrink (.int .i64)
private def limitedTy : Ty := .limited (.int .i64) 2

private def origins : Array Origin := #[⟨0, 1, "statement"⟩, ⟨0, 2, "expression"⟩,
  ⟨0, 3, "statement"⟩, ⟨0, 4, "statement"⟩, ⟨0, 5, "statement"⟩]

private def mkFunc (slots : Array Slot) (insts : List Inst) (summary : SummaryAnn := .unknown) : Func :=
  { name := "main"
    params := []
    results := []
    slots
    scopes := #[none]
    blocks := #[⟨[], insts⟩]
    summary
    org := none }

private def mkModule (slots : Array Slot) (insts : List Inst) : Module :=
  { files := #["shrink"]
    globals := #[]
    funcs := #[mkFunc slots insts]
    entry := 0
    origins
    profile := .shrink
    structs := #[] }

private def accepted (m : Module) : Bool := match validate m with
  | .ok () => true
  | .error _ => false

private def lowerAccepted (bytes : String) : Bool :=
  match Core.Decode.decodeBytes bytes.toUTF8 with
  | .error _ => false
  | .ok core => match Core.validate core with
    | .error _ => false
    | .ok () => accepted (Goose.Lower.lower core)

private def rejected (m : Module) (code : Code) : Bool := match validate m with
  | .ok () => false
  | .error e => e.code == code

private def returned (m : Module) (trace : String) : Bool := match run 100 .release m with
  | .done .returned output => output == trace
  | _ => false

private def aborted (m : Module) (kind : AbortKind) (origin : OriginId) (trace : String := "") : Bool :=
  match run 100 .release m with
  | .done (.aborted found originId) output => found == kind && originId == origin && output == trace
  | _ => false

private def decInst (profile : ArtifactProfile) (j : Lean.Json) : Bool :=
  match Json.decInst ⟨#[], 0, 0, 1, 0, 0, 0, profile⟩ j with
  | .ok _ => true
  | .error _ => false

private def rec (tag : String) (fields : Array Lean.Json) : Lean.Json :=
  .arr (#[.str tag] ++ fields)

private def summaryWire (profile : ArtifactProfile) (fields : Array Lean.Json) : Bool :=
  match Decode.decSummary profile 0 1 (rec "summary" fields) with
  | .ok _ => true
  | .error _ => false

private def emptyPilot : Module :=
  { files := #[]
    globals := #[]
    funcs := #[{ mkFunc #[] [.term (.ret [] none)] with scopes := #[] }]
    entry := 0
    origins := #[]
    profile := .pilot
    structs := #[] }

private def emptyPilotShape : Bool :=
  match Json.decodeBytes (Json.write emptyPilot).toUTF8 with
  | .ok m => m.profile == .pilot && m.funcs.size == 1 &&
      (m.funcs[0]?.map (fun f => f.summary == .unknown && f.blocks.size == 1)).getD false
  | .error _ => false

#guard emptyPilotShape
#guard summaryWire .pilot #[.arr #[], .arr #[], .arr #[], .arr #[], .num 0, .num 0]
#guard !summaryWire .pilot #[.arr #[], .arr #[], .arr #[], .arr #[], .arr #[], .num 0, .num 0]
#guard summaryWire .shrink #[.arr #[], .arr #[], .arr #[], .arr #[], .arr #[], .num 0, .num 0]
#guard !summaryWire .shrink #[.arr #[], .arr #[], .arr #[], .num 0, .num 0, .num 0]

#guard decInst .pilot (rec "i_push" #[.num 0, .num 1, .num 2, .arr #[]])
#guard !decInst .pilot (rec "i_push" #[.num 0, .num 1, .num 2])
#guard decInst .shrink (rec "i_pop" #[.num 0, .num 1, .arr #[.num 0]])
#guard decInst .shrink (rec "x_pop_n" #[.num 0, .num 1, .arr #[.num 0]])
#guard decInst .shrink (rec "x_resize" #[.num 0, .num 1, .arr #[.num 2], .arr #[.num 0]])
#guard decInst .shrink (rec "x_resize" #[.num 0, .num 1, .arr #[], .arr #[.num 0]])
#guard decInst .shrink (rec "x_clear" #[.num 0, .arr #[.num 0]])
#guard decInst .shrink (rec "x_replace" #[.num 0, .num 1, .arr #[.num 0]])
#guard !decInst .pilot (rec "i_pop" #[.num 0, .num 1, .arr #[.num 0]])
#guard !decInst .pilot (rec "x_pop_n" #[.num 0, .num 1, .arr #[.num 0]])
#guard !decInst .pilot (rec "x_resize" #[.num 0, .num 1, .arr #[], .arr #[.num 0]])
#guard !decInst .pilot (rec "x_clear" #[.num 0, .arr #[.num 0]])
#guard !decInst .pilot (rec "x_replace" #[.num 0, .num 1, .arr #[.num 0]])

private def popRun : Module := mkModule #[⟨growTy, .mutable, 0, 0⟩] [
  .eff (.enter 0),
  .def 0 (.constInt .i64 10), .def 1 (.constInt .i64 20),
  .def 2 (.arrLit growTy [0, 1]), .eff (.slotInit 0 2 (some 0)),
  .def 3 (.slotAddr 0), .def 4 (.pop 3 (some 1)),
  .eff (.print [.val 4] (some 2)), .def 5 (.constInt .i64 1),
  .eff (.popN 3 5 (some 3)), .def 6 (.arrayLen 3),
  .eff (.print [.val 6] (some 2)), .eff (.leave 0), .term (.ret [] none)]

#guard accepted popRun
#guard returned popRun "20\n0\n"

private def limitedKeptRef : Module := mkModule
  #[⟨limitedTy, .mutable, 0, 0⟩, ⟨.ref .mutable (.int .i64), .immutable, 0, 1⟩] [
  .eff (.enter 0), .def 0 (.constInt .i64 10),
  .def 1 (.arrLit limitedTy [0]), .eff (.slotInit 0 1 (some 0)),
  .def 2 (.slotAddr 0), .def 3 (.constInt .i64 20), .def 4 (.push 2 3 (some 1)),
  .eff (.slotInit 1 4 (some 0)), .eff (.clear 2 (some 2)),
  .def 5 (.slotAddr 1), .def 6 (.load 5), .def 7 (.load 6),
  .eff (.print [.val 7] (some 2)), .eff (.leave 0), .term (.ret [] none)]

#guard accepted limitedKeptRef
#guard returned limitedKeptRef "20\n"

private def deadResizableRef : Module := mkModule
  #[⟨growTy, .mutable, 0, 0⟩, ⟨.ref .mutable (.int .i64), .immutable, 0, 1⟩] [
  .eff (.enter 0), .def 0 (.constInt .i64 10),
  .def 1 (.arrLit growTy [0]), .eff (.slotInit 0 1 (some 0)),
  .def 2 (.slotAddr 0), .def 3 (.snapshot .owner 2), .def 4 (.constInt .i64 0),
  .def 5 (.indexChecked 3 4 (some 1)), .eff (.slotInit 1 5 (some 0)),
  .def 6 (.constInt .i64 1), .eff (.popN 2 6 (some 2)),
  .def 7 (.slotAddr 1), .def 8 (.load 7), .def 9 (.load 8),
  .eff (.print [.val 9] (some 2)), .eff (.leave 0), .term (.ret [] none)]

#guard accepted deadResizableRef
private def pathRangeFault (m : Module) : Bool := match run 100 .release m with
  | .fault .pathRange => true
  | _ => false
#guard pathRangeFault deadResizableRef

private def limitedResize (sizeTy : IntTy) (size : Int) (fill : Option Int) : Module :=
  let owner := limitedTy
  let fillOps := match fill with
    | none => []
    | some n => [.def 4 (.constInt .i64 n)]
  let fillValue := if fill.isSome then some 4 else none
  mkModule #[⟨owner, .mutable, 0, 0⟩] ([
    .eff (.enter 0), .def 0 (.constInt .i64 10), .def 1 (.arrLit owner [0]),
    .eff (.slotInit 0 1 (some 0)), .def 2 (.slotAddr 0),
    .def 3 (.constInt sizeTy size)] ++ fillOps ++ [
    .eff (.resize 2 3 fillValue (some 1)), .eff (.leave 0), .term (.ret [] none)])

#guard accepted (limitedResize .i64 1 (some 99))
#guard returned (limitedResize .i64 1 (some 99)) ""
#guard aborted (limitedResize .i64 3 none) .resizeFill 1
#guard aborted (limitedResize .i64 3 (some 99)) .capacity 1
#guard aborted (limitedResize .i64 (-1) (some 99)) .resizeNegative 1
#guard aborted (limitedResize .u64 9223372036854775808 (some 99)) .resizeNegative 1

private def replaceModule (clearFirst : Bool) : Module := mkModule
  #[⟨growTy, .mutable, 0, 0⟩] ([
    .eff (.enter 0), .def 0 (.constInt .i64 1),
    .def 1 (.arrLit growTy [0]), .eff (.slotInit 0 1 (some 0)),
    .def 2 (.slotAddr 0)] ++ (if clearFirst then [.eff (.clear 2 (some 1))] else []) ++ [
    .def 3 (.constInt .i64 2), .def 4 (.arrLit growTy [3]),
    .eff (.replace 2 4 (some 2)), .def 5 (.arrayLen 2),
    .eff (.print [.val 5] (some 3)), .eff (.leave 0), .term (.ret [] none)])

#guard accepted (replaceModule true)
#guard returned (replaceModule true) "1\n"
#guard rejected (replaceModule false) .v060

private def dependentReplace : Module := mkModule
  #[⟨growTy, .mutable, 0, 0⟩] [
    .eff (.enter 0), .def 0 (.constInt .i64 1), .def 1 (.arrLit growTy [0]),
    .eff (.slotInit 0 1 (some 0)), .def 2 (.slotAddr 0), .def 3 (.snapshot .owner 2),
    .def 4 (.constInt .i64 0), .def 5 (.indexChecked 3 4 (some 1)), .def 6 (.load 5),
    .def 7 (.arrLit growTy [6]), .eff (.clear 2 (some 2)),
    .eff (.replace 2 7 (some 3)), .eff (.leave 0), .term (.ret [] none)]

#guard rejected dependentReplace .v060

private def aliasedParameterReplace : Func :=
  { name := "aliased-parameters"
    params := [.ref .mutable growTy, .ref .mutable growTy]
    results := []
    slots := #[]
    scopes := #[]
    blocks := #[⟨[(0, .data (.ref .mutable growTy)), (1, .data (.ref .mutable growTy))], [
      .eff (.clear 0 (some 0)), .def 2 (.constInt .i64 7),
      .def 3 (.push 1 2 (some 1)), .def 4 (.arrLit growTy [2]),
      .eff (.replace 0 4 (some 2)), .term (.ret [] none)]⟩]
    summary := .unknown
    org := none }

private def aliasedParameterModule : Module :=
  { mkModule #[] [.term (.ret [] none)] with
    funcs := #[mkFunc #[] [.term (.ret [] none)], aliasedParameterReplace] }

#guard rejected aliasedParameterModule .v060

private def duplicateFanInReplace : Func :=
  { name := "duplicate-fan-in"
    params := [.ref .mutable growTy]
    results := []
    slots := #[]
    scopes := #[]
    blocks := #[
      ⟨[(0, .data (.ref .mutable growTy))], [
        .def 1 (.arrayLen 0), .def 2 (.constInt .i64 10),
        .def 3 (.arrLit growTy [2]), .def 4 (.arrLit growTy [1]),
        .def 5 (.constBool true), .eff (.clear 0 (some 0)),
        .term (.condbr 5 1 [] 16 [])]⟩,
      ⟨[], [.term (.condbr 5 2 [] 3 [])]⟩,
      ⟨[], [.term (.condbr 5 4 [] 5 [])]⟩,
      ⟨[], [.term (.condbr 5 6 [] 7 [])]⟩,
      ⟨[], [.term (.condbr 5 8 [] 9 [])]⟩,
      ⟨[], [.term (.condbr 5 10 [] 11 [])]⟩,
      ⟨[], [.term (.condbr 5 12 [] 13 [])]⟩,
      ⟨[], [.term (.condbr 5 14 [] 15 [])]⟩,
      ⟨[], [.term (.br 17 [3])]⟩,
      ⟨[], [.term (.br 17 [3])]⟩,
      ⟨[], [.term (.br 17 [3])]⟩,
      ⟨[], [.term (.br 17 [3])]⟩,
      ⟨[], [.term (.br 17 [3])]⟩,
      ⟨[], [.term (.br 17 [3])]⟩,
      ⟨[], [.term (.br 17 [3])]⟩,
      ⟨[], [.term (.br 17 [3])]⟩,
      ⟨[], [.term (.br 17 [4])]⟩,
      ⟨[(6, .data growTy)], [.term (.condbr 5 18 [6] 18 [6])]⟩,
      ⟨[(7, .data growTy)], [
        .eff (.replace 0 7 (some 1)), .term (.ret [] none)]⟩]
    summary := .unknown
    org := none }

private def duplicateFanInModule : Module :=
  { mkModule #[] [.term (.ret [] none)] with
    funcs := #[mkFunc #[] [.term (.ret [] none)], duplicateFanInReplace] }

#guard rejected duplicateFanInModule .v060

private def readBetweenClearAndReplace (throughCall : Bool) : Module :=
  let readFunc : Func :=
    { name := "read-owner"
      params := [.ref .mutable growTy]
      results := []
      slots := #[]
      scopes := #[]
      blocks := #[⟨[(0, .data (.ref .mutable growTy))], [
        .def 1 (.arrayLen 0), .term (.ret [] none)]⟩]
      roots := { params := #[(0, [.param 0])] }
      summary := .known ⟨[.param 0], [], [], [], [], false, false⟩
      org := none }
  let insts := if throughCall then [
    .eff (.clear 2 (some 0)), .def 3 (.call 1 [2] (some 1)),
    .def 4 (.arrLit growTy [0]), .eff (.replace 2 4 (some 2)),
    .eff (.leave 0), .term (.ret [] none)] else [
    .eff (.clear 2 (some 0)), .def 3 (.arrayLen 2),
    .def 4 (.arrLit growTy [0]), .eff (.replace 2 4 (some 2)),
    .eff (.leave 0), .term (.ret [] none)]
  let entry := mkFunc #[⟨growTy, .mutable, 0, 0⟩] ([
    .eff (.enter 0), .def 0 (.constInt .i64 1), .def 1 (.arrLit growTy [0]),
    .eff (.slotInit 0 1 (some 0)), .def 2 (.slotAddr 0)] ++ insts)
  { mkModule #[] [.term (.ret [] none)] with
    files := #["read"]
    funcs := if throughCall then #[entry, readFunc] else #[entry]
    profile := .shrink }

#guard rejected (readBetweenClearAndReplace false) .v060
#guard rejected (readBetweenClearAndReplace true) .v060

private def popSummaryFunc (shrinks : List Target) : Func :=
  { name := "pop-summary"
    params := [.ref .mutable growTy]
    results := []
    slots := #[]
    scopes := #[]
    blocks := #[⟨[(0, .data (.ref .mutable growTy))], [
      .def 1 (.pop 0 (some 0)), .term (.ret [] none)]⟩]
    roots := { params := #[(0, [.param 0])] }
    summary := .known ⟨[.param 0], [], [], shrinks, [], true, false⟩
    org := none }

private def summaryModule (shrinks : List Target) : Module :=
  let entry := { mkFunc #[] [.term (.ret [] none)] with name := "entry" }
  { files := #["summary"]
    globals := #[]
    funcs := #[entry, popSummaryFunc shrinks]
    entry := 0
    origins
    profile := .shrink
    structs := #[] }

#guard accepted (summaryModule [.param 0])
#guard rejected (summaryModule []) .v050

private def pushSummaryOmittingWrites : Func :=
  { name := "push-summary"
    params := [.ref .mutable growTy]
    results := []
    slots := #[]
    scopes := #[]
    blocks := #[⟨[(0, .data (.ref .mutable growTy))], [
      .def 1 (.constInt .i64 7), .def 2 (.push 0 1 (some 0)), .term (.ret [] none)]⟩]
    summary := .known ⟨[], [], [.param 0], [], [], false, false⟩
    org := none }

private def appendSummaryOmittingWrites : Func :=
  { name := "append-summary"
    params := [.ref .mutable growTy]
    results := []
    slots := #[]
    scopes := #[]
    blocks := #[⟨[(0, .data (.ref .mutable growTy))], [
      .def 1 (.snapshot .owner 0), .eff (.append 0 1 (some 0)), .term (.ret [] none)]⟩]
    summary := .known ⟨[.param 0], [], [.param 0], [], [], false, false⟩
    org := none }

private def writeOmissionModule (f : Func) : Module :=
  { (summaryModule [.param 0]) with funcs := #[
      { mkFunc #[] [.term (.ret [] none)] with name := "entry" }, f] }

#guard rejected (writeOmissionModule pushSummaryOmittingWrites) .v050
#guard rejected (writeOmissionModule appendSummaryOmittingWrites) .v050

private def letReplace : Module :=
  let ownerTy := .growshrink (.int .i64)
  { files := #["let-replace"]
    globals := #[]
    funcs := #[{ mkFunc #[⟨ownerTy, .immutable, 0, 0⟩] [
      .eff (.enter 0), .def 0 (.slotAddr 0), .eff (.clear 0 (some 0)),
      .def 1 (.arrLit ownerTy []), .eff (.replace 0 1 (some 1)),
      .eff (.leave 0), .term (.ret [] none)] with summary := .unknown }]
    entry := 0
    origins
    profile := .shrink
    structs := #[] }

#guard rejected letReplace .v030

private def pilotLetGrowPushAppend : Module :=
  let growTy := Ty.grow (.int .i64)
  { (mkModule #[⟨growTy, .immutable, 0, 0⟩] [
      .eff (.enter 0), .def 0 (.constInt .i64 10),
      .def 1 (.arrLit growTy [0]), .eff (.slotInit 0 1 (some 0)),
      .def 2 (.slotAddr 0), .def 3 (.constInt .i64 20),
      .def 4 (.push 2 3 none), .def 5 (.snapshot .owner 2),
      .eff (.append 2 5 (some 0)), .def 6 (.arrayLen 2),
      .eff (.print [.val 6] (some 0)), .eff (.leave 0), .term (.ret [] none)]) with
    profile := .pilot }

#guard accepted pilotLetGrowPushAppend
#guard returned pilotLetGrowPushAppend "4\n"

private def readonlyPop : Module :=
  let bad := { popSummaryFunc [.param 0] with
    params := [.ref .readOnly growTy]
    blocks := #[⟨[(0, .data (.ref .readOnly growTy))], [
      .def 1 (.pop 0 (some 0)), .term (.ret [] none)]⟩]
    summary := .unknown }
  let entry := { mkFunc #[] [.term (.ret [] none)] with name := "entry" }
  { files := #["readonly"]
    globals := #[]
    funcs := #[entry, bad]
    entry := 0
    origins
    profile := .shrink
    structs := #[] }

#guard rejected readonlyPop .v030

#guard lowerAccepted (include_str "../../../test/semantics/golden/grow_let_reference_replace.core.json")
#guard lowerAccepted (include_str "../../../test/semantics/golden/shrink_let_reference_replace.core.json")

end Goose.GIR.ShrinkChecks
