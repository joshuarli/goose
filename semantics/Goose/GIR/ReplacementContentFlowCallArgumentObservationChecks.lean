import Goose.GIR.ReplacementContentFlow

namespace Goose.GIR.ReplacementContentFlowCallArgumentObservationChecks

open Goose.Core

private def element := Ty.int .i64
private def slice := Ty.slice .readOnly element
private def holder := Ty.ref .mutable slice
private def function (name : String) (params results : List Ty) (parameters : List (ValueId × VTy))
    (instructions : List Inst) (roots : RootInfo := {}) : Func :=
  { name,params,results,slots := #[],scopes := #[none],blocks := #[⟨parameters,instructions⟩]
    roots,summary := .unknown,org := some 0 }

private def sample (array : Ty) : Module :=
  let global : Global :=
    { name := "array",ty := array,kind := .mutable,org := 0
      init := function "init" [] [array] []
        [.def 0 (.constInt .i64 0),.def 1 (.arrLit array [0]),.term (.ret [1] (some 0))] }
  let reader := function "reader" [] [slice] []
    [.def 0 (.globalAddr 0),.def 1 (.snapshot .borrowed 0),
     .def 2 (.viewSlice .readOnly 1 .omitted .omitted (some 0)),.term (.ret [2] (some 0))]
    { results := #[[.global 0]] }
  let ignore := function "ignore" [slice] [element] [(0,.data slice)]
    [.def 1 (.constInt .i64 0),.term (.ret [1] (some 0))] { params := #[(0,[.param 0])] }
  let entry := function "entry" [] [] []
    [.def 0 (.call 0 [] (some 0)),.def 1 (.call 1 [0] (some 0)),.term (.ret [] (some 0))]
  let specialized := function "specialized" [slice] [] [(0,.data slice)]
    [.def 1 (.call 1 [0] (some 0)),.term (.ret [] (some 0))] { params := #[(0,[.global 0])] }
  let contents := function "contents" [holder] [] [(0,.data holder)]
    [.def 1 (.load 0),.def 2 (.call 1 [1] (some 0)),.term (.ret [] (some 0))]
    { params := #[(0,[.param 0])],contents := #[(0,[.global 0])] }
  { files := #["slice-call-argument"],funcs := #[reader,ignore,entry,specialized,contents],globals := #[global],entry := 2
    origins := #[⟨0,1,"expr"⟩],profile := .shrink }

private def flow (module : Module) (index : Nat) : Option ReplacementFunctionFlow := do
  let func ← module.funcs[index]?
  pure ((replacementContentFlow module).forFunction func (func.valueTypes module))

private def fixed := sample (.arr element 1)
private def owner := sample (.growshrink element)

#guard (flow fixed 2).bind (·.value 0) == some [.global 0]
#guard (flow fixed 2).bind (·.call 0 []) == some []
#guard (flow fixed 2).bind (·.call 1 [0]) == some []
#guard (flow owner 2).bind (·.call 1 [0]) == some [.global 0]
#guard (flow fixed 3).bind (·.value 0) == some [.global 0]
#guard (flow fixed 3).bind (·.call 1 [0]) == some [.global 0]
#guard (flow fixed 4).bind (·.value 1) == some [.global 0]
#guard (flow fixed 4).bind (·.call 1 [1]) == some [.global 0]

end Goose.GIR.ReplacementContentFlowCallArgumentObservationChecks
