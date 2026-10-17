import Goose.GIR.ReplacementContentFlow

namespace Goose.GIR.ReplacementContentFlowBoundsChecks

open Goose.Core ReplacementContentFlow.Model

private def element := Ty.int .i64
private def owner := Ty.growshrink element
private def slice := Ty.slice .mutable element
private def holder := Ty.ref .mutable slice

private def function (name : String) (params results : List Ty) (slots : Array Slot)
    (instructions : List Inst) (roots : RootInfo := {}) : Func :=
  { name, params, results, slots, scopes := #[none]
    blocks := #[⟨params.zipIdx.map (fun (type, index) => (index, .data type)), instructions⟩]
    roots, summary := .unknown, org := some 0 }

private def global : Global :=
  { name := "global", ty := owner, kind := .mutable, org := 0
    init := function "init" [] [owner] #[]
      [.def 0 (.arrLit owner []), .term (.ret [0] (some 0))] }

private def module (functions : Array Func) (globals : Array Global := #[]) : Module :=
  { files := #["content-bounds"], globals
    funcs := functions.push (function "entry" [] [] #[]
      [.def 0 (.constInt .i64 0), .term (.ret [] (some 0))])
    entry := functions.size, origins := #[⟨0, 1, "expr"⟩], profile := .shrink }

private def flow (m : Module) (f : Func) : ReplacementFunctionFlow :=
  (replacementContentFlow m).forFunction f (f.valueTypes m)

private def reader := function "reader" [holder, slice] [slice] #[]
  [.def 2 (.load 0), .term (.ret [2] (some 0))]
  { params := #[(0, [.param 0]), (1, [.param 1])]
    contents := #[(0, [.param 1])], results := #[[.param 1]] }

private def wide := function "wide" [holder, slice, slice] [] #[⟨slice, .mutable, 0, 3⟩]
  [.eff (.slotInit 0 1 (some 0)), .def 3 (.slotAddr 0), .def 4 (.load 3),
   .def 5 (.call 1 [0, 4] (some 0)), .term (.ret [] (some 0))]
  { params := #[(0, [.param 0]), (1, [.param 1]), (2, [.param 2])]
    contents := #[(0, [.param 1, .param 2])] }

private def wideModule := module #[wide, reader]
#guard (flow wideModule (wideModule.funcs[2]'(by decide))).value 0 == some []
#guard (flow wideModule wide).value 4 == some [.param 1]
#guard ((flow wideModule wide).value 5).any fun roots =>
  roots.contains (.param 1) && roots.contains (.param 2)
#guard ((flow wideModule wide).call 1 [0, 4]).any fun roots => roots.contains (.param 2)

private def fixedReader := { reader with
  roots := { reader.roots with params := #[(0, [.param 0]), (1, [.global 0, .global 1])] } }
private def fixedWide := { wide with
  roots := { params := #[(0, [.param 0]), (1, [.global 0]), (2, [.global 1])], contents := #[(0, [.global 0, .global 1])] } }
private def fixedModule := module #[fixedWide, fixedReader] #[global, global]
#guard (flow fixedModule (fixedModule.funcs[2]'(by decide))).value 0 == some []
#guard (flow fixedModule fixedWide).value 4 == some [.global 0]
#guard ((flow fixedModule fixedWide).value 5).any fun roots => roots.contains (.global 1)

private def tooNarrowReader := { fixedReader with
  roots := { fixedReader.roots with params := #[(0, [.param 0]), (1, [.global 0])] } }
#guard (flow (module #[fixedWide, tooNarrowReader] #[global, global]) fixedWide).value 5 == none

private def actual (index : Nat) : Option (List RootRef) :=
  if index == 1 then some [.global 0] else some []
#guard admittedArgumentBound reader actual 1 == some .callerStorage
#guard admittedArgumentBound reader (fun _ => none) 1 == none
#guard admittedArgumentBound reader actual 2 == none
#guard contentInputBound reader actual [.local 0] == none
#guard ContentInputBound.callerStorage.covers none == false
#guard ContentInputBound.callerStorage.covers (some [])
#guard ContentInputBound.callerStorage.covers (some [.local 0, .global 0, .param 0])

private def missingRow := { reader with roots := { reader.roots with params := #[(0, [.param 0])] } }
#guard admittedArgumentBound missingRow actual 1 == some (.roots [.global 0])
#guard (flow (module #[wide, missingRow]) wide).value 5 == none
private def emptyRow := { reader with roots := { reader.roots with params := #[(0, [.param 0]), (1, [])] } }
#guard admittedArgumentBound emptyRow (fun _ => some []) 1 == some (.roots [])
#guard (contentInputBound emptyRow (fun _ => some []) [.param 1]).any
  (fun upper => !upper.covers (some [.global 0]))
private def scalarParameter := { reader with params := [holder, element] }
#guard admittedArgumentBound scalarParameter (fun _ => some []) 1 == some (.roots [])
#guard (contentInputBound scalarParameter (fun _ => some []) [.param 1]).any
  (fun upper => !upper.covers (some [.global 0]))
#guard admittedArgumentBound fixedReader (fun _ => some []) 1 ==
  some (.roots [.global 0, .global 1])
#guard (contentInputBound fixedReader (fun _ => some []) [.param 1]).any
  (fun upper => !upper.covers (some [.local 0]))
#guard contentInputBound reader (fun index => if index == 1 then some [] else none)
  [.param 1, .param 0] == none

private def unknownHolder : Func :=
  { wide with
    blocks := #[⟨[(0, .data holder), (1, .data slice), (2, .data slice)],
      [.def 3 (.call 1 [0, 1] (some 0)), .term (.ret [] (some 0))]⟩]
    roots := { wide.roots with contents := #[] } }
#guard (flow (module #[unknownHolder, reader]) unknownHolder).value 3 == none
#guard (flow (module #[unknownHolder, reader])
  ((module #[unknownHolder, reader]).funcs[2]'(by decide))).value 0 == none

private def forward := function "forward" [holder, slice, slice] [] #[]
  [.def 3 (.call 0 [0, 1, 2] (some 0)), .term (.ret [] (some 0))] wide.roots
private def nestedModule := module #[wide, reader, forward]
#guard ((flow nestedModule forward).call 0 [0, 1, 2]).any fun roots =>
  roots.contains (.param 2)

private def mutator := function "mutator" [holder, slice] [] #[]
  [.def 2 (.load 0), .def 3 (.sliceView 2), .def 4 (.constInt .i64 0),
   .def 5 (.indexChecked 3 4 (some 0)), .def 6 (.constInt .i64 7),
   .eff (.store 5 6 (some 0)), .term (.ret [] (some 0))] reader.roots
private def mutationCaller := function "mutationCaller" [] []
  #[⟨owner, .mutable, 0, 0⟩, ⟨slice, .mutable, 0, 1⟩]
  [.def 0 (.arrLit owner []), .eff (.slotInit 0 0 (some 0)),
   .def 1 (.slotAddr 0), .def 2 (.snapshot .owner 1),
   .def 3 (.viewSlice .mutable 2 .omitted .omitted (some 0)),
   .def 4 (.globalAddr 0), .def 5 (.snapshot .owner 4),
   .def 6 (.viewSlice .mutable 5 .omitted .omitted (some 0)),
   .eff (.slotInit 1 6 (some 0)), .def 7 (.slotAddr 1),
   .def 8 (.call 1 [7, 3] (some 0)), .term (.ret [] (some 0))]
private def mutationModule := module #[mutationCaller, { mutator with roots := { mutator.roots with results := #[] } }] #[global]
#guard ((flow mutationModule mutationCaller).call 1 [7, 3]).any fun roots =>
  roots.contains (.global 0) && roots.contains (.local 0)
#guard (flow mutationModule mutationCaller).value 3 == some [.local 0]
#guard (flow mutationModule mutationCaller).value 6 == some [.global 0]

private def initializer : Func :=
  { mutationCaller with
    name := "initializer"
    results := [element]
    blocks := #[⟨[], (mutationCaller.blocks[0]'(by decide)).insts.dropLast ++
      [.def 9 (.constInt .i64 0), .term (.ret [9] (some 0))]⟩] }
private def initializerGlobal : Global :=
  { name := "scalar", ty := element, kind := .mutable, org := 0, init := initializer }
private def initializerModule := module
  #[mutationCaller, { mutator with roots := { mutator.roots with results := #[] } }]
  #[global, initializerGlobal]
#guard ((flow initializerModule initializer).call 1 [7, 3]).any
  (·.contains (.global 0))
#guard (flow initializerModule initializer).value 3 == some [.local 0]

private def mixed := function "mixed" [slice] [] #[] [.term (.ret [] (some 0))]
  { params := #[(0, [.param 0, .global 0])] }
private def mixedCaller := function "mixedCaller" [holder] [] #[]
  [.def 1 (.load 0), .def 2 (.call 1 [1] (some 0)), .term (.ret [] (some 0))]
  { params := #[(0, [.param 0])], contents := #[(0, [.global 1])] }
private def mixedModule := module #[mixedCaller, mixed] #[global, global]
#guard (flow mixedModule mixedCaller).value 1 == some [.global 1]
#guard ((flow mixedModule mixedCaller).call 1 [1]).any (·.contains (.global 1))
private def noSelf := { mixed with roots := { params := #[(0, [.global 0])] } }
#guard (flow (module #[mixedCaller, noSelf] #[global, global]) mixedCaller).value 1 == none

end Goose.GIR.ReplacementContentFlowBoundsChecks
