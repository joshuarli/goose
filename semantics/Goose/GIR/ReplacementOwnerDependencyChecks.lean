import Goose.Core.Validate
import Goose.GIR.Validate
import Goose.Lower.CoreToGir
import Goose.GIR.ReplacementContentFlow

namespace Goose.Lower.Validation
open Goose.Core Goose.GIR
private def input : Core.Module :=
  let element := Ty.int .i64
  let fixed := Ty.arr element 1
  let owner := Ty.growshrink element
  let slice := Ty.slice .readOnly element
  let main : Core.Impl :=
    { name := "main",params := #[],results := #[],vars := #[],body := .mk 0 [] none,summary := .unknown }
  let receiver : Core.Impl :=
    { name := "receiver",params := #[⟨0,.byRef⟩],results := #[],
      vars := #[⟨"p",.ref .mutable owner,.immutable,0,0⟩],
      body := .mk 0 [.assignWhole (.deref (.read (.var 0)))
        (.arrLit owner [.len (.val (.call 2 [] 0))]) 0] none,summary := .unknown }
  let reader : Core.Impl :=
    { name := "reader",params := #[],results := #[slice],vars := #[],
      body := .mk 0 [] (some (.slice .readOnly (.of (.global 0)) .omitted .omitted 0)),summary := .unknown }
  { files := #["slice-observation"],types := #[],
    globals := #[⟨"fixed",fixed,.immutable,.arrLit fixed [.lit .i64 0],0⟩],
    impls := #[main,receiver,reader],contexts := #[⟨0,"main",[],[],[]⟩,
      ⟨1,"receiver",[(0,[.param 0])],[],[]⟩,⟨2,"reader",[],[[.global 0]],[]⟩],
    entry := 0,origins := #[⟨0,1,"expr"⟩],profile := .shrink }
#guard (Core.validate input).toBool
private def module := lower input
private def receiver := module.funcs[1]?.getD { name := "absent",params := [],results := [],slots := #[],scopes := #[],blocks := #[],summary := .unknown,org := none }
private def flow := (replacementContentFlow module).forFunction receiver (receiver.valueTypes module)
#guard (GIR.validate module).toBool
#guard flow.value 3 == some [.global 0]
#guard flow.ownerDependencies 3 == some []
#guard (replacementQueries module receiver (receiver.valueTypes module)).value 3 == some [.global 0]
#guard (replacementQueries module receiver (receiver.valueTypes module)).ownerDependencies 3 == some []

private def ownerGlobalInput : Core.Module :=
  let owner := Ty.growshrink (.int .i64)
  { input with globals := #[⟨"owner", owner, .mutable, .arrLit owner [.lit .i64 0], 0⟩] }

#guard !(Core.validate ownerGlobalInput).toBool
#guard match GIR.validate (lower ownerGlobalInput) with
  | .error violation => violation.code == .v060
  | .ok _ => false

private def nestedInput : Core.Module :=
  let element := Ty.int .i64
  let fixed := Ty.arr element 1
  let owner := Ty.growshrink element
  let slice := Ty.slice .readOnly element
  let main : Core.Impl :=
    { name := "main",params := #[],results := #[],vars := #[],body := .mk 0 [] none,summary := .unknown }
  let receiver : Core.Impl :=
    { name := "receiver",params := #[⟨0,.byRef⟩],results := #[],
      vars := #[⟨"p",.ref .mutable owner,.immutable,0,0⟩],
      body := .mk 0 [.assignWhole (.deref (.read (.var 0)))
        (.arrLit owner [.call 3 [.byVal (.call 2 [] 0)] 0]) 0] none,summary := .unknown }
  let reader : Core.Impl :=
    { name := "reader",params := #[],results := #[slice],vars := #[],
      body := .mk 0 [] (some (.slice .readOnly (.of (.global 0)) .omitted .omitted 0)),summary := .unknown }
  let ignore : Core.Impl :=
    { name := "ignore", params := #[⟨0,.byValue⟩], results := #[element],
      vars := #[⟨"unused",slice,.immutable,0,0⟩], body := .mk 0 [] (some (.lit .i64 0)),
      summary := .known ⟨[],[],[],[],[],false,false⟩ }
  { files := #["slice-observation"],types := #[],
    globals := #[⟨"fixed",fixed,.immutable,.arrLit fixed [.lit .i64 0],0⟩],
    impls := #[main,receiver,reader,ignore],contexts := #[⟨0,"main",[],[],[]⟩,
      ⟨1,"receiver",[(0,[.param 0])],[],[]⟩,⟨2,"reader",[],[[.global 0]],[]⟩,⟨3,"ignore",[(0,[.global 0])],[[]],[]⟩],
    entry := 0,origins := #[⟨0,1,"expr"⟩],profile := .shrink }
#guard (Core.validate nestedInput).toBool
#guard (GIR.validate (lower nestedInput)).toBool

private def nestedOwnerGlobalInput : Core.Module :=
  { nestedInput with globals := ownerGlobalInput.globals }

#guard !(Core.validate nestedOwnerGlobalInput).toBool
#guard match GIR.validate (lower nestedOwnerGlobalInput) with
  | .error violation => violation.code == .v060
  | .ok _ => false

private def boundaryFunction : Func :=
  { name := "boundary", params := [.ref .mutable (.growshrink (.int .i64))],
    results := [], slots := #[], scopes := #[], blocks := #[], summary := .unknown,
    org := none, roots := { params := #[(0, [.global 0])], contents := #[(0, [.global 0])] } }

private def boundaryModule (type : Ty) : GIR.Module :=
  let initial : Func :=
    { name := "init", params := [], results := [type], slots := #[], scopes := #[],
      blocks := #[], summary := .unknown, org := none }
  let global : GIR.Global :=
    { name := "storage", ty := type, kind := .mutable, init := initial, org := 0 }
  { funcs := #[], globals := #[global], entry := 0, profile := .shrink,
    structs := #[], files := #[], origins := #[] }

private def boundaryQueries (m : GIR.Module) (owner : RootRef)
    (source : ReplacementContentFlow.Model.Roots) : ReplacementQueries :=
  { values := #[some [owner], ReplacementContentFlow.Model.normalize boundaryFunction source],
    dependencies := #[some [owner], ReplacementContentFlow.Model.ownerDependencies m boundaryFunction source],
    callRoots := fun _ _ => none }

private def boundaryTransfer (m : GIR.Module) (owner : RootRef)
    (source : ReplacementContentFlow.Model.Roots) : List ValueId :=
  transferEmptyInst m #[some (.data (.ref .mutable (.growshrink (.int .i64)))),
      some (.data (.slice .readOnly (.int .i64)))]
    (boundaryQueries m owner source) [0] (.def 2 (.sliceView 1))

#guard boundaryTransfer (boundaryModule (.arr (.int .i64) 1)) (.param 0) (.known [.global 0]) == [0]
#guard boundaryTransfer (boundaryModule (.growshrink (.int .i64))) (.param 0) (.known [.global 0]) == []
#guard boundaryTransfer (boundaryModule (.arr (.int .i64) 1)) (.param 0) (.known [.param 0]) == []
#guard boundaryTransfer (boundaryModule (.arr (.int .i64) 1)) (.param 0) (.known [.contents 0]) == []
#guard boundaryTransfer (boundaryModule (.arr (.int .i64) 1)) (.local 0) (.known [.local 0]) == []
#guard boundaryTransfer (boundaryModule (.arr (.int .i64) 1)) (.param 0) .unknown == []
#guard boundaryTransfer (boundaryModule (.arr (.int .i64) 1)) (.param 0) (.known [.global 9]) == []
#guard boundaryTransfer (boundaryModule (.ref .mutable (.int .i64))) (.param 0) (.known [.global 0]) == []

private def callBoundaryModule (type : Ty) (reads : List Target) : GIR.Module :=
  let callee : Func :=
    { boundaryFunction with
      params := [.slice .readOnly (.int .i64)]
      summary := .known ⟨reads,[],[],[],[],false,false⟩
      roots := { params := #[(0, [.param 0])] } }
  { (boundaryModule type) with funcs := #[callee] }

private def callBoundaryTransfer (m : GIR.Module) (owner : RootRef)
    (source : ReplacementContentFlow.Model.Roots) : List ValueId :=
  let queries := { boundaryQueries m owner source with callRoots := fun _ _ => some [] }
  transferEmptyInst m #[some (.data (.ref .mutable (.growshrink (.int .i64)))),
      some (.data (.slice .readOnly (.int .i64)))] queries [0] (.def 2 (.call 0 [1] none))

#guard callBoundaryTransfer (callBoundaryModule (.arr (.int .i64) 1) []) (.param 0) (.known [.global 0]) == [0]
#guard callBoundaryTransfer (callBoundaryModule (.arr (.int .i64) 1) [.param 0]) (.param 0) (.known [.global 0]) == [0]
#guard callBoundaryTransfer (callBoundaryModule (.arr (.int .i64) 1) [.global 0]) (.param 0) (.known [.global 0]) == []
#guard callBoundaryTransfer (callBoundaryModule (.growshrink (.int .i64)) []) (.param 0) (.known [.global 0]) == []
#guard callBoundaryTransfer (callBoundaryModule (.arr (.int .i64) 1) []) (.param 0) (.known [.param 0]) == []
#guard callBoundaryTransfer (callBoundaryModule (.arr (.int .i64) 1) []) (.param 0) (.known [.contents 0]) == []
#guard callBoundaryTransfer (callBoundaryModule (.arr (.int .i64) 1) []) (.local 0) (.known [.local 0]) == []
#guard callBoundaryTransfer (callBoundaryModule (.arr (.int .i64) 1) []) (.param 0) .unknown == []
#guard callBoundaryTransfer (callBoundaryModule (.arr (.int .i64) 1) []) (.param 0) (.known [.global 9]) == []
#guard callBoundaryTransfer (callBoundaryModule (.ref .mutable (.int .i64)) []) (.param 0) (.known [.global 0]) == []
end Goose.Lower.Validation
