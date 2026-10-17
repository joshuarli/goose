import Goose.GIR.AdmittedRegions
import Goose.GIR.Json
import Goose.GIR.Validate
import Goose.Core.Validate
import Goose.Lower.CoreToGir

namespace Goose.GIR.AdmittedRegionsChecks

open Goose.Core Goose.Lower

set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

private def int := Ty.int .i64
private def slice := Ty.slice .mutable int
private def holder := Ty.ref .mutable slice
private def owner := Ty.growshrink int
private def function (name : String) (params : List Ty) (slots : Array Slot)
    (instructions : List Inst) (roots : RootInfo := {}) : Func :=
  { name, params, results := [], slots, scopes := #[none]
    blocks := #[⟨params.zipIdx.map (fun (type,index) => (index,.data type)),
      [.eff (.enter 0)] ++ instructions.dropLast ++ [.eff (.leave 0)] ++
        instructions.drop (instructions.length - 1)⟩]
    roots, summary := .unknown, org := some 0 }
private def module (funcs : Array Func) (globals : Array Global := #[]) : Module :=
  { files := #["regions"], globals, funcs, entry := 0,
    origins := #[⟨0,1,"call"⟩], profile := .shrink }
private def admitted (m : Module) : Bool :=
  (m.checkAdmittedRegions m.implTypes (resultRoots m m.implTypes) m.rootCount).isOk
private def rootsChecked (m : Module) : Bool :=
  (checkRootAnnotations m m.implTypes (resultRoots m m.implTypes) m.rootCount).isOk
private def table : Json.Tables :=
  { types := #[], nGlobals := 1, nFuncs := 0, nOrigins := 0,
    nSlots := 2, nScopes := 0, nBlocks := 0 }
private def decodeRoots (text : String) : Except String RootInfo := do
  Json.decRootInfo table 1 1 (← Lean.Json.parse text)

#guard Json.wRootInfo { results := #[[]] } == "[\"roots\",[],[],[[]]]"
#guard (decodeRoots "[\"roots\",[],[],[[]]]").toOption.any (·.slots.isNone)
#guard Json.wRootInfo { results := #[[]], slots := some #[] } == "[\"roots\",[],[],[[]],[]]"
#guard (decodeRoots "[\"roots\",[],[],[[]],[]]").toOption.any (·.slots == some #[])
#guard (decodeRoots "[\"roots\",[],[],[[]],[[\"sr\",1,[[\"r_local\",1],[\"r_param\",0],[\"r_global\",0]]]]]").isOk
#guard (decodeRoots "[\"roots\",[],[],[[]],[[\"sr\",2,[]]]]").isOk == false
#guard (decodeRoots "[\"roots\",[],[],[[]],[[\"sr\",0,[[\"r_param\",1]]]]]").isOk == false
#guard (decodeRoots "[\"roots\",[],[],[[]],[[\"sr\",0,[]],[\"sr\",0,[]]]]").isOk == false

#guard (decodeRoots "[\"roots\",[],[],[[]]]").toOption.any fun roots =>
  Json.wRootInfo roots == "[\"roots\",[],[],[[]]]"
#guard (decodeRoots "[\"roots\",[],[],[[]],[]]").toOption.any fun roots =>
  Json.wRootInfo roots == "[\"roots\",[],[],[[]],[]]"
#guard (decodeRoots "[\"roots\",[],[],[[]],[[\"sr\",1,[[\"r_local\",1]]]]]").toOption.any fun roots =>
  Json.wRootInfo roots == "[\"roots\",[],[],[[]],[[\"sr\",1,[[\"r_local\",1]]]]]"
#guard (decodeRoots "[\"roots\",[],[],[[]],[[\"sr\",0,[[\"r_local\",2]]]]]").isOk == false
#guard (decodeRoots "[\"roots\",[],[],[[]],[[\"sr\",0,[[\"r_global\",1]]]]]").isOk == false

private def slotTest : Func :=
  function "slots" [] #[⟨slice,.mutable,0,0⟩] [.term (.ret [] (some 0))]
    { slots := some #[(0,[.global 0])] }
#guard (slotTest.checkAdmittedRegions (module #[slotTest]) #[] ⟨#[[.global 0]],#[]⟩).isOk
#guard (slotTest.checkAdmittedRegions (module #[slotTest]) #[] ⟨#[[.global 1]],#[]⟩).isOk == false
#guard (({ slotTest with roots := { slots := some #[(1,[])] } } : Func).checkAdmittedRegions
  (module #[slotTest]) #[] ⟨#[[]],#[]⟩).isOk == false
#guard (({ slotTest with slots := #[⟨int,.mutable,0,0⟩] } : Func).checkAdmittedRegions
  (module #[slotTest]) #[] ⟨#[[]],#[]⟩).isOk == false
#guard (ReplacementContentFlow.Model.start slotTest #[]).slots[0]? == some .pending

private def resultTest : Func :=
  { function "result" [] #[] [.term (.ret [0] (some 0))]
      { results := #[[.global 0]], slots := some #[] } with results := [slice] }
#guard (resultTest.checkAdmittedRegions (module #[resultTest]) #[some (.data slice)] ⟨#[],#[[.global 1]]⟩).isOk == false
#guard (resultTest.checkAdmittedRegions (module #[resultTest]) #[some (.data slice)] ⟨#[],#[[.global 0]]⟩).isOk

#guard (resultTest.checkAdmittedRegions (module #[resultTest]) #[some (.data owner)]
  ⟨#[],#[[.global 1]]⟩).isOk

private def widenedLocal : Core.Module :=
  { files := #["widened-local.goose"], types := #[], globals := #[],
    impls := #[
      { name := "main", params := #[], results := #[], vars := #[],
        body := .mk 0 [.expr (.lit .i64 0) 0] none, summary := .unknown },
      { name := "wrapper", params := #[⟨0,.byRef⟩,⟨1,.byValue⟩,⟨2,.byValue⟩], results := #[],
        vars := #[⟨"holder",.ref .mutable (.slice .mutable .bool),.immutable,0,0⟩,
                  ⟨"a",.slice .mutable .bool,.immutable,0,0⟩,
                  ⟨"b",.slice .mutable .bool,.immutable,0,0⟩,
                  ⟨"wide",.slice .mutable .bool,.immutable,0,0⟩],
        body := .mk 0 [.letS 3 (.read (.var 1)) 0,
          .expr (.call 2 [.byRef .mutable (.deref (.read (.var 0))), .byVal (.read (.var 3))] 0) 0] none,
        summary := .unknown },
      { name := "callee", params := #[⟨0,.byRef⟩,⟨1,.byValue⟩], results := #[],
        vars := #[⟨"holder",.ref .mutable (.slice .mutable .bool),.immutable,0,0⟩,
                  ⟨"value",.slice .mutable .bool,.immutable,0,0⟩],
        body := .mk 0 [] none, summary := .unknown }],
    contexts := #[⟨0,"main",[],[],[]⟩,
      ⟨1,"wrapper",[(0,[.param 0]),(1,[.param 1]),(2,[.param 2]),(3,[.param 1,.param 2])],[],[(0,[.param 1,.param 2])]⟩,
      ⟨2,"callee",[(0,[.param 0]),(1,[.param 1])],[],[(0,[.param 1])]⟩],
    entry := 0, origins := #[⟨0,1,"call"⟩] }
example : Core.validate widenedLocal = .ok () := by cbv
#guard admitted (lower widenedLocal)
#guard rootsChecked (lower widenedLocal)
#guard !(rootsChecked { lower widenedLocal with funcs :=
  ((lower widenedLocal).funcs.map fun f => { f with roots := { f.roots with slots := none } }) })

private def widenedGlobals : Core.Module :=
  { files := #["widened-globals.goose"], types := #[],
    globals := #[⟨"G0",.arr int 1,.mutable,.arrLit (.arr int 1) [.lit .i64 0],0⟩,
      ⟨"G1",.arr int 1,.mutable,.arrLit (.arr int 1) [.lit .i64 1],0⟩],
    impls := #[
      { name := "main", params := #[], results := #[],
        vars := #[⟨"wide",slice,.immutable,0,0⟩,⟨"holder",slice,.mutable,0,0⟩],
        body := .mk 0 [
          .letS 0 (.slice .mutable (.of (.global 0)) .omitted .omitted 0) 0,
          .letS 1 (.slice .mutable (.of (.global 1)) .omitted .omitted 0) 0,
          .expr (.call 1 [.byRef .mutable (.var 1),.byVal (.read (.var 0))] 0) 0] none,
        summary := .unknown },
      { name := "callee", params := #[⟨0,.byRef⟩,⟨1,.byValue⟩], results := #[],
        vars := #[⟨"holder",holder,.immutable,0,0⟩,⟨"value",slice,.immutable,0,0⟩],
        body := .mk 0 [] none, summary := .known ⟨[],[],[],[],[],false,false⟩ },
      { name := "producer", params := #[], results := #[slice], vars := #[],
        body := .mk 0 [] (some (.slice .mutable (.of (.global 0)) .omitted .omitted 0)),
        summary := .known ⟨[.global 0],[],[],[],[],true,false⟩ }],
    contexts := #[⟨0,"main",[(0,[.global 0,.global 1]),(1,[.global 0,.global 1])],[],[]⟩,
      ⟨1,"callee",[(0,[.param 0]),(1,[.param 1])],[],[(0,[.param 1])]⟩,
      ⟨2,"producer",[],[[.global 0,.global 1]],[]⟩],
    entry := 0, origins := #[⟨0,1,"call"⟩], profile := .pilot }
example : Core.validate widenedGlobals = .ok () := by cbv
#guard admitted (lower widenedGlobals)
#guard rootsChecked (lower widenedGlobals)
private def widenedReturn : Core.Module :=
  { widenedGlobals with impls := widenedGlobals.impls.modify 0 fun impl =>
    { impl with body := .mk 0 [
      .letS 0 (.call 2 [] 0) 0,
      .letS 1 (.slice .mutable (.of (.global 1)) .omitted .omitted 0) 0,
      .expr (.call 1 [.byRef .mutable (.var 1),.byVal (.read (.var 0))] 0) 0] none } }
example : Core.validate widenedReturn = .ok () := by cbv
#guard admitted (lower widenedReturn)
#guard rootsChecked (lower widenedReturn)
#guard (resultRoots (lower widenedReturn) (lower widenedReturn).implTypes)[2]?.getD [] ==
  [.global 0,.global 1]
#guard (resultRoots { lower widenedReturn with funcs :=
    ((lower widenedReturn).funcs.map fun f => { f with roots := { f.roots with slots := none } }) }
  (lower widenedReturn).implTypes)[2]?.getD [] == [.global 0]

private def storeTest : Func :=
  function "store" [holder,slice] #[] [.eff (.store 0 1 (some 0)),.term (.ret [] (some 0))]
    { params := #[(0,[.param 0]),(1,[.param 1])], contents := #[(0,[])], slots := some #[] }
#guard !admitted (module #[storeTest])
#guard admitted (module #[{ storeTest with roots := { storeTest.roots with contents := #[(0,[.param 1])] } }])

private def callee : Func :=
  { function "callee" [holder,slice] #[]
    [.def 2 (.load 0), .def 3 (.sliceView 2), .def 4 (.constInt .i64 0),
     .def 5 (.indexChecked 3 4 (some 0)), .def 6 (.constInt .i64 7),
     .eff (.store 5 6 (some 0)), .term (.ret [] (some 0))]
    { params := #[(0,[.param 0]),(1,[.param 1])], contents := #[(0,[.param 1])], slots := some #[] }
    with summary := .known ⟨[.param 0],[.param 1],[],[],[],true,false⟩ }
private def caller : Func :=
  { function "caller" [] #[⟨owner,.mutable,0,0⟩,⟨slice,.mutable,0,1⟩]
    [.def 0 (.constInt .i64 0), .def 1 (.arrLit owner [0]), .eff (.slotInit 0 1 (some 0)),
     .def 2 (.slotAddr 0), .def 3 (.snapshot .owner 2),
     .def 4 (.viewSlice .mutable 3 .omitted .omitted (some 0)),
     .def 5 (.globalAddr 0), .def 6 (.snapshot .owner 5),
     .def 7 (.viewSlice .mutable 6 .omitted .omitted (some 0)),
     .eff (.slotInit 1 7 (some 0)), .def 8 (.slotAddr 1),
     .def 9 (.call 1 [8,4] (some 0)), .term (.ret [] (some 0))]
    { slots := some #[(1,[.global 0])] }
    with summary := .known ⟨[.global 0],[],[],[],[],true,false⟩ }
private def global : Global :=
  { name := "P", ty := owner, kind := .mutable, org := 0,
    init := { function "init" [] #[] [.def 0 (.arrLit owner []), .term (.ret [0] (some 0))]
      with results := [owner], roots := { results := #[[]] } } }
private def unsafeEffect : Module := module #[caller,callee] #[global]
#guard !admitted unsafeEffect
#guard !rootsChecked unsafeEffect
#guard (caller.summaryClosed (caller.effects unsafeEffect
  (caller.provenance (resultRoots unsafeEffect unsafeEffect.implTypes)
    (caller.valueTypes unsafeEffect) unsafeEffect.rootCount))).isOk

private def phiCallee : Func :=
  { function "phi.callee" [holder] #[]
    [.def 1 (.globalAddr 1), .def 2 (.snapshot .owner 1),
     .def 3 (.viewSlice .mutable 2 .omitted .omitted (some 0)),
     .eff (.store 0 3 (some 0)), .term (.ret [] (some 0))]
    { params := #[(0,[.param 0])], contents := #[(0,[.global 0,.global 1])], slots := some #[] }
    with summary := .known ⟨[.global 1],[.param 0],[],[],[.param 0],false,false⟩ }
private def phiCaller : Func :=
  { name := "phi.main", params := [], results := [],
    slots := #[⟨slice,.mutable,0,0⟩,⟨slice,.mutable,0,1⟩], scopes := #[none],
    blocks := #[
      ⟨[],[.eff (.enter 0), .def 0 (.globalAddr 0), .def 1 (.snapshot .owner 0),
        .def 2 (.viewSlice .mutable 1 .omitted .omitted (some 0)), .eff (.slotInit 0 2 (some 0)),
        .def 3 (.globalAddr 1), .def 4 (.snapshot .owner 3),
        .def 5 (.viewSlice .mutable 4 .omitted .omitted (some 0)), .eff (.slotInit 1 5 (some 0)),
        .def 6 (.slotAddr 0), .def 7 (.slotAddr 1), .def 8 (.constBool true),
        .term (.condbr 8 1 [6] 1 [7])]⟩,
      ⟨[(9,.data holder)],[.def 10 (.call 1 [9] (some 0)), .def 11 (.slotAddr 0),
        .def 12 (.load 11), .def 13 (.sliceView 12), .def 14 (.constInt .i64 0),
        .def 15 (.indexChecked 13 14 (some 0)), .def 16 (.constInt .i64 7),
        .eff (.store 15 16 (some 0)), .eff (.leave 0), .term (.ret [] (some 0))]⟩],
    roots := { slots := some #[(0,[.global 0]),(1,[.global 1])] },
    summary := .known ⟨[.global 0,.global 1],[.global 0],[],[],[],true,false⟩, org := some 0 }
private def phiModule : Module := module #[phiCaller,phiCallee] #[global,{ global with name := "Q" }]
private def phiProv : Prov := phiCaller.provenance
  (resultRoots phiModule phiModule.implTypes) (phiCaller.valueTypes phiModule) phiModule.rootCount
#guard rootsChecked phiModule
#guard (argumentContents phiCaller phiProv 9).all
  (mapContentRoots phiCaller phiProv [9] [.global 0,.global 1]).contains
#guard (mapContentRoots phiCaller phiProv [9] [.global 0,.global 1]).all
  (argumentContents phiCaller phiProv 9).contains
#guard !admitted phiModule
#guard (phiCaller.summaryClosed (phiCaller.effects phiModule phiProv)).isOk

private def headerGlobal : Global :=
  { name := "header", ty := slice, kind := .mutable, org := 0,
    init := { function "header.init" [] #[]
      [.def 0 (.globalAddr 0), .def 1 (.snapshot .owner 0),
       .def 2 (.viewSlice .mutable 1 .omitted .omitted (some 0)),
       .term (.ret [2] (some 0))] { results := #[[.global 0]] } with results := [slice] } }
private def headerAliasCallee : Func :=
  { function "header.alias" [holder] #[]
    [.def 1 (.globalAddr 2), .def 2 (.snapshot .owner 1),
     .def 3 (.viewSlice .mutable 2 .omitted .omitted (some 0)),
     .def 4 (.globalAddr 1), .eff (.store 4 3 (some 0)),
     .def 5 (.load 0), .def 6 (.sliceView 5), .def 7 (.constInt .i64 0),
     .def 8 (.indexChecked 6 7 (some 0)), .def 9 (.constInt .i64 7),
     .eff (.store 8 9 (some 0)), .term (.ret [] (some 0))]
    { params := #[(0,[.global 1])], contents := #[(0,[.global 1])] }
    with summary := .known ⟨[.param 0,.global 2],[.global 1],[],[],[],true,false⟩ }
private def headerAliasCaller : Func :=
  { function "header.main" [] #[]
    [.def 0 (.globalAddr 1), .def 1 (.call 1 [0] (some 0)), .term (.ret [] (some 0))]
    with summary := .known ⟨[.global 1,.global 2],[.global 1],[],[],[],true,false⟩ }
private def legacyHeaderAlias : Module :=
  module #[headerAliasCaller,headerAliasCallee] #[global,headerGlobal,{ global with name := "Q" }]
#guard rootsChecked legacyHeaderAlias
#guard (validate legacyHeaderAlias).isOk
#guard admitted legacyHeaderAlias
#guard !admitted { legacyHeaderAlias with funcs := legacyHeaderAlias.funcs.modify 0 fun f =>
  { f with roots := { f.roots with slots := some #[] } } }

private def referenceGlobal : Global := { global with ty := slice }
#guard !admitted (module #[resultTest] #[referenceGlobal])
#guard admitted (module #[{ resultTest with roots := { resultTest.roots with slots := none } }] #[referenceGlobal])
#guard !admitted (module #[function "old" [] #[] [.term (.ret [] (some 0))]]
  #[{ referenceGlobal with init := { referenceGlobal.init with roots := { slots := some #[] } } }])

end Goose.GIR.AdmittedRegionsChecks
