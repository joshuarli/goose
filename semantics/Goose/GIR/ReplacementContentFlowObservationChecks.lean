import Goose.GIR.ReplacementContentFlow

namespace Goose.GIR.ReplacementContentFlowObservationChecks

open Goose.Core

private def element := Ty.int .i64
private def slice := Ty.slice .readOnly element

private def function (name : String) (results : List Ty) (instructions : List Inst)
    (roots : RootInfo := {}) : Func :=
  { name,params := [],results,slots := #[],scopes := #[none],blocks := #[⟨[],instructions⟩]
    roots,summary := .unknown,org := some 0 }

private def sample (array : Ty) : Module :=
  let global : Global :=
    { name := "array",ty := array,kind := .mutable,org := 0
      init := function "init" [array]
        [.def 0 (.constInt .i64 0),.def 1 (.arrLit array [0]),.term (.ret [1] (some 0))] }
  let reader := function "reader" [slice]
    [.def 0 (.globalAddr 0),.def 1 (.snapshot .borrowed 0),
     .def 2 (.viewSlice .readOnly 1 .omitted .omitted (some 0)),.term (.ret [2] (some 0))]
    { results := #[[.global 0]] }
  let caller := function "entry" []
    [.def 0 (.call 0 [] (some 0)),.def 1 (.sliceView 0),.def 2 (.viewLen 1),.term (.ret [] (some 0))]
  { files := #["slice-observation"],funcs := #[reader,caller],globals := #[global],entry := 1
    origins := #[⟨0,1,"expr"⟩],profile := .shrink }

private def flow (module : Module) : Option ReplacementFunctionFlow := do
  let caller ← module.funcs[1]?
  pure ((replacementContentFlow module).forFunction caller (caller.valueTypes module))

private def fixed := sample (.arr element 1)
private def owner := sample (.growshrink element)

#guard (flow fixed).bind (·.value 0) == some [.global 0]
#guard (flow fixed).bind (·.value 1) == some [.global 0]
#guard (flow fixed).bind (·.call 0 []) == some []
#guard (flow owner).bind (·.value 0) == some [.global 0]
#guard (flow owner).bind (·.call 0 []) == some [.global 0]
#guard ReplacementContentFlow.Model.ownerTouches fixed [.param 0,.local 0,.global 1] ==
  [.param 0,.local 0,.global 1]

#guard (flow fixed).bind (·.ownerDependencies 0) == some []
#guard (flow owner).bind (·.ownerDependencies 0) == some [.global 0]

private def ownerParameter : Func :=
  { name := "ownerParameter",params := [.ref .mutable (.growshrink element)],results := [],slots := #[],
    scopes := #[none],blocks := #[⟨[(0,.data (.ref .mutable (.growshrink element)))],
      [.term (.ret [] (some 0))]⟩],roots := { params := #[(0,[.global 0])] },
    summary := .unknown,org := some 0 }
private def specializedModule := { fixed with funcs := fixed.funcs.push ownerParameter }
private def parameterFlow := (replacementContentFlow specializedModule).forFunction ownerParameter
  (ownerParameter.valueTypes specializedModule)
#guard parameterFlow.value 0 == some [.global 0]
#guard parameterFlow.ownerDependencies 0 == some [.global 0]

private def holder := Ty.ref .mutable slice
private def contentReader : Func :=
  { name := "contentReader",params := [holder],results := [element],slots := #[],scopes := #[none],
    blocks := #[⟨[(0,.data holder)], [.def 1 (.load 0),.def 2 (.sliceView 1),
      .def 3 (.viewLen 2),.term (.ret [3] (some 0))]⟩],
    roots := { params := #[(0,[.param 0])],contents := #[(0,[.global 0])] },summary := .unknown,org := some 0 }
private def contentCaller : Func :=
  { name := "contentCaller",params := [slice],results := [],slots := #[⟨slice,.mutable,0,0⟩],scopes := #[none],
    blocks := #[⟨[(0,.data slice)], [.eff (.slotInit 0 0 (some 0)),.def 1 (.slotAddr 0),
      .def 2 (.call 0 [1] (some 0)),.term (.ret [] (some 0))]⟩],
    roots := { params := #[(0,[.global 0])] },summary := .unknown,org := some 0 }
private def contentModule := { fixed with funcs := #[contentReader,contentCaller,function "entry" [] [.term (.ret [] (some 0))]],entry := 2 }
private def readerFlow := (replacementContentFlow contentModule).forFunction contentReader (contentReader.valueTypes contentModule)
private def callerFlow := (replacementContentFlow contentModule).forFunction contentCaller (contentCaller.valueTypes contentModule)
#guard readerFlow.ownerDependencies 1 == some [.global 0]
#guard callerFlow.call 0 [1] == some [.local 0,.global 0]

private def noRoots := function "noRoots" [] [.term (.ret [] (some 0))]
#guard ReplacementContentFlow.Model.ownerDependencies fixed noRoots .pending == none
#guard ReplacementContentFlow.Model.ownerDependencies fixed noRoots .unknown == none
#guard ReplacementContentFlow.Model.ownerDependencies fixed noRoots (.known []) == some []
#guard ReplacementContentFlow.Model.ownerDependencies fixed noRoots (.known [.global 1]) == some [.global 1]
private def opaqueGlobals := { fixed with globals := fixed.globals.modify 0 fun global =>
  { global with ty := .ref .readOnly (.growshrink element) } }
#guard ReplacementContentFlow.Model.ownerDependencies opaqueGlobals noRoots (.known [.global 0]) == some [.global 0]

end Goose.GIR.ReplacementContentFlowObservationChecks
