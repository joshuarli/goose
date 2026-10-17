import Goose.GIR.ReplacementContentFlow

namespace Goose.GIR.ReplacementContentFlowChecks

open Goose.Core

private def element := Ty.int .i64
private def owner := Ty.growshrink element
private def slice := Ty.slice .readOnly element
private def holder := Ty.ref .mutable slice

private def function (name : String) (params results : List Ty) (slots : Array Slot)
    (instructions : List Inst) (roots : RootInfo := {}) : Func :=
  { name, params, results, slots, scopes := #[none]
    blocks := #[⟨params.zipIdx.map (fun (type, index) => (index, .data type)), instructions⟩]
    roots, summary := .unknown, org := some 0 }

private def global (type : Ty) : Global :=
  { name := "global", ty := type, kind := .mutable, org := 0
    init := function "init" [] [type] #[]
      [.def 0 (if type.ownerElem?.isSome then .arrLit type [] else .constInt .i64 0),
       .term (.ret [0] (some 0))] }

private def module (functions : Array Func) (globals : Array Global := #[]) : Module :=
  { files := #["content-flow"], globals
    funcs := functions.push (function "entry" [] [] #[] [.term (.ret [] (some 0))])
    entry := functions.size
    origins := #[⟨0, 1, "expr"⟩], profile := .shrink }

private def localFlow (m : Module) (f : Func) : ReplacementFunctionFlow :=
  (replacementContentFlow m).forFunction f (f.valueTypes m)

private def writer := function "writer" [holder, slice] [] #[]
  [.eff (.store 0 1 (some 0)), .term (.ret [] (some 0))]
  { params := #[(0, [.param 0]), (1, [.param 1])], contents := #[(0, [.param 1])] }

private def overwritten := function "overwritten" [slice] []
  #[⟨owner, .mutable, 0, 0⟩, ⟨slice, .mutable, 0, 1⟩]
  [.def 1 (.arrLit owner []), .eff (.slotInit 0 1 (some 0)),
   .def 2 (.slotAddr 0), .eff (.slotInit 1 0 (some 0)), .def 3 (.slotAddr 1),
   .def 4 (.snapshot .owner 2), .def 5 (.viewSlice .readOnly 4 .omitted .omitted (some 0)),
   .def 6 (.call 1 [3, 5] (some 0)), .eff (.clear 2 (some 0)),
   .def 7 (.load 3), .def 8 (.sliceView 7), .def 9 (.viewSlice .readOnly 8 .omitted .omitted (some 0)),
   .term (.ret [] (some 0))]
  { params := #[(0, [])] }

private def overwrittenModule := module #[overwritten, writer]
#guard (localFlow overwrittenModule overwritten).value 0 == some []
#guard ((localFlow overwrittenModule overwritten).value 7).any (·.contains (.local 0))
#guard ((localFlow overwrittenModule overwritten).value 8).any (·.contains (.local 0))
#guard ((localFlow overwrittenModule overwritten).value 9).any (·.contains (.local 0))
#guard (localFlow overwrittenModule overwritten).mutation 1 [3, 5] == some [.local 1]

private def identity := function "identity" [slice] [slice] #[]
  [.term (.ret [0] (some 0))] { params := #[(0, [.param 0])], results := #[[.param 0]] }
private def returnAlias : Func := { overwritten with blocks := #[⟨[(0, .data slice)],
  ((overwritten.blocks[0]?).map Block.insts |>.getD []).dropLast ++ [.def 10 (.call 2 [7] (some 0)), .term (.ret [] (some 0))]⟩] }
private def returnAliasModule := module #[returnAlias, writer, identity]
#guard ((localFlow returnAliasModule returnAlias).value 10).any (·.contains (.local 0))

private def scalar := function "scalar" [] [element] #[]
  [.def 0 (.globalAddr 0), .def 1 (.load 0), .term (.ret [1] (some 0))]
private def scalarCaller := function "scalarCaller" [] [] #[]
  [.def 0 (.call 1 [] (some 0)), .term (.ret [] (some 0))]
private def scalarModule := module #[scalarCaller, scalar] #[global element]
#guard (localFlow scalarModule scalarCaller).call 1 [] == some []

private def pure := function "pure" [] [element] #[]
  [.def 0 (.constInt .i64 1), .term (.ret [0] (some 0))]
private def chain := function "chain" [] [element] #[]
  [.def 0 (.call 1 [] (some 0)), .term (.ret [0] (some 0))]
private def chainModule := module #[chain, pure]
#guard (localFlow chainModule chain).call 1 [] == some []
private def recursive := function "recursive" [] [element] #[]
  [.def 0 (.call 0 [] (some 0)), .term (.ret [0] (some 0))]
#guard (localFlow (module #[recursive]) recursive).call 0 [] == some []

private def unused := function "unused" [holder] [element] #[]
  [.def 1 (.constInt .i64 1), .term (.ret [1] (some 0))]
  { params := #[(0, [.param 0])] }
private def forwardUnused := function "forwardUnused" [holder] [element] #[]
  [.def 1 (.call 1 [0] (some 0)), .term (.ret [1] (some 0))]
  { params := #[(0, [.param 0])] }
private def unusedModule := module #[forwardUnused, unused]
#guard (localFlow unusedModule forwardUnused).call 1 [0] == some [.param 0]

private def staleNonempty := { overwritten with
  roots := { params := #[(0, [.global 0])] } }
private def nonemptyWriter := { writer with
  roots := { writer.roots with contents := #[(0, [.global 0, .param 1])] } }
private def staleNonemptyModule := module #[staleNonempty, nonemptyWriter] #[global owner]
#guard ((localFlow staleNonemptyModule staleNonempty).value 7).any fun roots =>
  roots.contains (.global 0) && roots.contains (.local 0)

private def forgedWriter := { writer with roots := { writer.roots with contents := #[(0, [])] } }
private def forgedModule := module #[overwritten, forgedWriter]
#guard (localFlow forgedModule overwritten).value 7 == none

private def seedless := function "seedless" [] [slice] #[⟨slice, .mutable, 0, 0⟩]
  [.def 0 (.slotAddr 0), .def 1 (.load 0), .eff (.slotInit 0 1 (some 0)), .term (.ret [1] (some 0))]
#guard (localFlow (module #[seedless]) seedless).value 1 == none
#guard ((replacementContentFlow scalarModule).forFunction scalar #[]).value 0 == none
#guard (localFlow (module #[scalar] #[global holder]) scalar).value 0 == none

private def aliasWriter := function "aliasWriter" [holder, holder, slice] [slice] #[]
  [.eff (.store 0 2 (some 0)), .def 3 (.load 1), .term (.ret [3] (some 0))]
  { params := #[(0, [.param 0]), (1, [.param 1]), (2, [.param 2])]
    contents := #[(0, [.global 0, .global 1]), (1, [.global 0])], results := #[[.global 0]] }
private def aliasCaller := function "aliasCaller" [slice, slice] [] #[⟨slice, .mutable, 0, 0⟩]
  [.eff (.slotInit 0 0 (some 0)), .def 2 (.slotAddr 0),
   .def 3 (.call 1 [2, 2, 1] (some 0)), .term (.ret [] (some 0))]
  { params := #[(0, [.global 0]), (1, [.global 1])] }
private def aliasModule := module #[aliasCaller, aliasWriter] #[global owner, global owner]
#guard (localFlow aliasModule aliasCaller).value 3 == none

private def contentReader := function "contentReader" [holder] [element] #[]
  [.def 1 (.load 0), .def 2 (.sliceView 1), .def 3 (.viewLen 2), .term (.ret [3] (some 0))]
  { params := #[(0, [.param 0])], contents := #[(0, [.global 0])] }
private def readerCaller := function "readerCaller" [slice] [] #[⟨slice, .mutable, 0, 0⟩]
  [.eff (.slotInit 0 0 (some 0)), .def 1 (.slotAddr 0),
   .def 2 (.call 1 [1] (some 0)), .term (.ret [] (some 0))]
  { params := #[(0, [.global 0])] }
private def readerModule := module #[readerCaller, contentReader] #[global owner]
#guard ((localFlow readerModule readerCaller).call 1 [1]).any fun roots =>
  roots.contains (.local 0) && roots.contains (.global 0)

private def emptyContentReader := { contentReader with
  roots := { contentReader.roots with contents := #[(0, [])] } }
private def initializerCaller := function "initializerCaller" [] [element]
  #[⟨slice, .mutable, 0, 0⟩]
  [.def 0 (.globalAddr 0), .def 1 (.snapshot .owner 0),
   .def 2 (.viewSlice .readOnly 1 .omitted .omitted (some 0)),
   .eff (.slotInit 0 2 (some 0)), .def 3 (.slotAddr 0),
   .def 4 (.call 0 [3] (some 0)), .term (.ret [4] (some 0))]
private def initializerModule := module #[emptyContentReader]
  #[global owner, { global element with init := initializerCaller }]
#guard (localFlow initializerModule emptyContentReader).value 1 == none

private def recursiveGlobal := function "recursiveGlobal" [] [element] #[]
  [.def 0 (.globalAddr 0), .def 1 (.load 0), .def 2 (.call 0 [] (some 0)),
   .term (.ret [1] (some 0))]
private def recursiveGlobalModule := module #[recursiveGlobal] #[global element]
#guard (localFlow recursiveGlobalModule recursiveGlobal).call 0 [] == some []

private def constantEmpty := function "constantEmpty" [slice] [slice] #[]
  [.term (.ret [0] (some 0))] { params := #[(0, [])], results := #[[]] }
private def constantEmptyModule := module #[constantEmpty]
#guard (localFlow constantEmptyModule constantEmpty).value 0 == some []

private def readerInitializerModule := module #[contentReader]
  #[global owner, { global element with init := initializerCaller }]
#guard ((localFlow readerInitializerModule contentReader).value 1).any (·.contains (.global 0))

private def invalidEntry := { constantEmptyModule with entry := 0 }
#guard (localFlow invalidEntry constantEmpty).value 0 == none

private def phiEmpty : Func :=
  { function "phiEmpty" [slice] [slice] #[] [] { params := #[(0, [])], results := #[[]] } with
    blocks := #[⟨[(0, .data slice)], [.def 1 (.constBool true), .term (.condbr 1 1 [0] 2 [0])]⟩,
      ⟨[(2, .data slice)], [.term (.br 3 [2])]⟩,
      ⟨[(3, .data slice)], [.term (.br 3 [3])]⟩,
      ⟨[(4, .data slice)], [.term (.ret [4] (some 0))]⟩] }
#guard (localFlow (module #[phiEmpty]) phiEmpty).value 4 == some []

private def phiNonempty : Func :=
  { function "phiNonempty" [slice, slice] [slice] #[] []
      { params := #[(0, []), (1, [.global 0])], results := #[[.global 0]] } with
    blocks := #[⟨[(0, .data slice), (1, .data slice)],
        [.def 2 (.constBool true), .term (.condbr 2 1 [0] 2 [1])]⟩,
      ⟨[(3, .data slice)], [.term (.br 3 [3])]⟩,
      ⟨[(4, .data slice)], [.term (.br 3 [4])]⟩,
      ⟨[(5, .data slice)], [.term (.ret [5] (some 0))]⟩] }
#guard (localFlow (module #[phiNonempty] #[global owner]) phiNonempty).value 5 == some [.global 0]

private def seedlessPhi : Func :=
  { function "seedlessPhi" [] [] #[] [] with
    blocks := #[⟨[], [.term (.br 1 [0])]⟩, ⟨[(0, .data slice)], [.term (.br 1 [0])]⟩] }
#guard (localFlow (module #[seedlessPhi]) seedlessPhi).value 0 == none

private def invalidScalarReturn := function "invalidScalarReturn" [] [element] #[]
  [.def 0 (.globalAddr 0), .term (.ret [0] (some 0))]
#guard (localFlow (module #[invalidScalarReturn] #[global owner]) invalidScalarReturn).value 0 == none

#guard (localFlow scalarModule scalarCaller).call 1 [0] == none
#guard (localFlow overwrittenModule overwritten).mutation 1 [3] == none

private def emptyAliasStore := function "emptyAliasStore" [.ref .readOnly slice, slice, holder] [slice] #[]
  [.eff (.store 2 1 (some 0)), .def 3 (.load 0), .term (.ret [3] (some 0))]
  { params := #[(0, [.param 0]), (1, []), (2, [.param 2])], contents := #[(0, [])], results := #[[]] }
#guard (localFlow (module #[emptyAliasStore]) emptyAliasStore).value 3 == some []

private def recursiveReference := function "recursiveReference" [] [.ref .readOnly element] #[]
  [.def 0 (.call 0 [] (some 0)), .term (.ret [0] (some 0))] { results := #[[]] }
private def recursiveReferenceModule := module #[recursiveReference, pure]
#guard (localFlow recursiveReferenceModule pure).value 0 == some []
#guard (localFlow recursiveReferenceModule recursiveReference).value 0 == some []

private def forgedReturnBound := function "forgedReturnBound" [] [.ref .mutable owner] #[]
  [.def 0 (.globalAddr 0), .term (.ret [0] (some 0))] { results := #[[]] }
private def forgedReturnModule := module #[forgedReturnBound, pure] #[global owner]
#guard (localFlow forgedReturnModule pure).value 0 == none

private def globalReturnBound := { forgedReturnBound with roots := { results := #[[.global 0]] } }
private def globalReturnModule := module #[globalReturnBound, pure] #[global owner]
#guard (localFlow globalReturnModule globalReturnBound).value 0 == some [.global 0]

private def genericReceiver := function "genericReceiver" [.ref .mutable owner] [] #[]
  [.eff (.clear 0 (some 0)), .def 1 (.call 1 [] (some 0)), .term (.ret [] (some 0))]
  { params := #[(0, [.param 0])] }
private def genericScalarReadModule := module #[genericReceiver, scalar] #[global element]
#guard (localFlow genericScalarReadModule genericReceiver).call 1 [] == some []

private def scalarWriter := function "scalarWriter" [] [element] #[]
  [.def 0 (.globalAddr 0), .def 1 (.constInt .i64 1), .eff (.store 0 1 (some 0)),
   .term (.ret [1] (some 0))]
private def genericScalarWriteModule := module #[genericReceiver, scalarWriter] #[global element]
#guard (localFlow genericScalarWriteModule genericReceiver).call 1 [] == some []

private def ownerReader := function "ownerReader" [] [element] #[]
  [.def 0 (.globalAddr 0), .def 1 (.arrayLen 0), .term (.ret [1] (some 0))]
private def genericOwnerReadModule := module #[genericReceiver, ownerReader] #[global owner]
#guard (localFlow genericOwnerReadModule genericReceiver).call 1 [] == some [.global 0]

private def scalarRefReader := function "scalarRefReader" [.ref .readOnly element] [element] #[]
  [.def 1 (.load 0), .term (.ret [1] (some 0))] { params := #[(0, [.param 0])] }
private def scalarRefCaller := function "scalarRefCaller" [] [] #[]
  [.def 0 (.globalAddr 0), .def 1 (.refFreeze 0), .def 2 (.call 1 [1] (some 0)),
   .term (.ret [] (some 0))]
private def scalarRefModule := module #[scalarRefCaller, scalarRefReader] #[global element]
#guard (localFlow scalarRefModule scalarRefCaller).call 1 [1] == some [.global 0]
#guard ReplacementContentFlow.Model.ownerTouches scalarModule [.global 20] == [.global 20]
#guard ReplacementContentFlow.Model.ownerTouches (module #[pure] #[global holder]) [.global 0] == [.global 0]

private def loadOnlyReader := function "loadOnlyReader" [holder] [] #[]
  [.def 1 (.load 0), .term (.ret [] (some 0))]
  { params := #[(0, [.param 0])], contents := #[(0, [.global 0])] }
private def loadOnlyModule := module #[readerCaller, loadOnlyReader] #[global owner]
#guard ((localFlow loadOnlyModule readerCaller).call 1 [1]).any (·.contains (.global 0))

private def forwardedOnlyReader := { loadOnlyReader with blocks := #[⟨[(0, .data holder)],
  [.def 1 (.load 0), .def 2 (.sliceView 1),
   .def 3 (.viewSlice .readOnly 2 .omitted .omitted (some 0)), .term (.ret [] (some 0))]⟩] }
private def forwardedOnlyModule := module #[readerCaller, forwardedOnlyReader] #[global owner]
#guard ((localFlow forwardedOnlyModule readerCaller).call 1 [1]).any (·.contains (.global 0))

private def crossContentCallee := function "crossContentCallee" [holder, holder] [element] #[]
  [.def 2 (.constInt .i64 1), .term (.ret [2] (some 0))]
  { params := #[(0, [.param 0]), (1, [.param 1])], contents := #[(0, [.param 1]), (1, [])] }
private def crossContentWrapper := function "crossContentWrapper" [holder, holder] [] #[]
  [.def 2 (.call 1 [0, 1] (some 0)), .term (.ret [] (some 0))]
  { params := #[(0, [.param 0]), (1, [.param 1])], contents := #[(0, [.param 1]), (1, [])] }
private def crossContentModule := module #[crossContentWrapper, crossContentCallee, pure]
#guard (localFlow crossContentModule pure).value 0 == some []

end Goose.GIR.ReplacementContentFlowChecks
