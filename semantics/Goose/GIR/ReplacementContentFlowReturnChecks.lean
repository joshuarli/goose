import Goose.GIR.ReplacementContentFlow

namespace Goose.GIR.ReplacementContentFlowReturnChecks

open Goose.Core

private def element := Ty.int .i64
private def owner := Ty.growshrink element
private def slice := Ty.slice .readOnly element

private def function (name : String) (results : List Ty) (instructions : List Inst)
    (roots : RootInfo := {}) : Func :=
  { name, params := [], results, slots := #[], scopes := #[none]
    blocks := #[⟨[],instructions⟩], roots, summary := .unknown, org := some 0 }

private def global : Global :=
  { name := "owner", ty := owner, kind := .mutable, org := 0
    init := function "init" [owner]
      [.def 0 (.constInt .i64 0),.def 1 (.arrLit owner [0]),.term (.ret [1] (some 0))] }

private def broadReturn (selected : GlobalId) := function "broadReturn" [slice]
  [.def 0 (.globalAddr selected),.def 1 (.snapshot .owner 0),
   .def 2 (.viewSlice .readOnly 1 .omitted .omitted (some 0)),.term (.ret [2] (some 0))]
  { results := #[[.global 0,.global 1]] }

private def consume (fn : FnId) := function "consume" []
  [.def 0 (.call fn [] (some 0)),.def 1 (.sliceView 0),.def 2 (.viewLen 1),.term (.ret [] (some 0))]

private def module (functions : Array Func) (extraGlobals : Array Global := #[]) : Module :=
  { files := #["return-flow"],funcs := functions,globals := #[global,global] ++ extraGlobals
    entry := functions.size - 1,origins := #[⟨0,1,"expr"⟩],profile := .shrink }

private def flow (m : Module) (f : Func) :=
  (replacementContentFlow m).forFunction f (f.valueTypes m)

private def independent := module #[broadReturn 1,consume 0]
private def dependent := module #[broadReturn 0,consume 0]
#guard (flow independent (consume 0)).value 0 == some [.global 1]
#guard (flow independent (consume 0)).value 1 == some [.global 1]
#guard (flow independent (consume 0)).call 0 [] == some [.global 1]
#guard (flow dependent (consume 0)).value 0 == some [.global 0]
#guard (flow dependent (consume 0)).call 0 [] == some [.global 0]

private def recursive := function "recursive" [slice]
  [.def 0 (.call 0 [] (some 0)),.term (.ret [0] (some 0))]
  { results := #[[.global 0,.global 1]] }
private def recursiveModule := module #[recursive,consume 0]
#guard (flow recursiveModule recursive).value 0 == some []
#guard (flow recursiveModule (consume 0)).value 0 == some []

private def recursiveBase : Func :=
  { recursive with blocks := #[
      ⟨[],[.def 0 (.constBool true),.term (.condbr 0 1 [] 2 [])]⟩,
      ⟨[],[.def 1 (.call 0 [] (some 0)),.term (.ret [1] (some 0))]⟩,
      ⟨[],[.def 2 (.globalAddr 1),.def 3 (.snapshot .owner 2),
        .def 4 (.viewSlice .readOnly 3 .omitted .omitted (some 0)),.term (.ret [4] (some 0))]⟩] }
private def recursiveBaseModule := module #[recursiveBase,consume 0]
#guard (flow recursiveBaseModule recursiveBase).value 1 == some [.global 1]
#guard (flow recursiveBaseModule (consume 0)).value 0 == some [.global 1]
#guard (flow recursiveBaseModule (consume 0)).call 0 [] == some [.global 1]

private def forwarder := function "forwarder" [slice]
  [.def 0 (.call 0 [] (some 0)),.term (.ret [0] (some 0))]
  { results := #[[.global 0,.global 1]] }
private def nestedModule := module #[broadReturn 1,forwarder,consume 1]
#guard (flow nestedModule forwarder).value 0 == some [.global 1]
#guard (flow nestedModule (consume 1)).value 0 == some [.global 1]

private def initializer := function "consumerInit" [element]
  [.def 0 (.call 0 [] (some 0)),.def 1 (.sliceView 0),.def 2 (.viewLen 1),.term (.ret [2] (some 0))]
private def initializerModule := module #[broadReturn 1,consume 0]
  #[{ name := "length",ty := element,kind := .immutable,org := 0,init := initializer }]
#guard (flow initializerModule initializer).value 0 == some [.global 1]
#guard (flow initializerModule initializer).call 0 [] == some [.global 1]

private def forged := { broadReturn 1 with roots := { results := #[[.global 0]] } }
private def forgedModule := module #[forged,consume 0]
#guard (flow forgedModule (consume 0)).value 0 == none

end Goose.GIR.ReplacementContentFlowReturnChecks
