import Goose.Lower.CoreToGir
import Goose.Core.Validate
import Goose.GIR.Validate
namespace Goose.Lower.Validation.ReplacementEmptyContentChecks

open Goose Goose.Core Goose.Lower
private def fixture : Core.Module :=
  let owner := Ty.growshrink (.int .i64)
  let receiver : Impl :=
    { name := "replace", params := #[⟨0, .byRef⟩], results := #[],
      vars := #[⟨"q", .ref .readOnly (.slice .readOnly (.int .i64)), .immutable, 0, 0⟩,
        ⟨"p", owner, .mutable, 0, 0⟩],
      body := .mk 0 [.letS 1 (.arrLit owner []) 0,
        .assignWhole (.var 1) (.arrLit owner [.len (.val (.read (.deref (.read (.var 0)))))]) 0] none,
      summary := .unknown }
  let main : Impl :=
    { name := "main", params := #[], results := #[], vars := #[], body := .mk 0 [] none, summary := .unknown }
  { files := #["replacement-empty-content"], types := #[],
    globals := #[],
    impls := #[main, receiver], contexts := #[⟨0, "main", [], [], []⟩,
      ⟨1, "replace", [(0, [.param 0])], [], [(0, [])]⟩],
    entry := 0, origins := #[⟨0, 1, "expr"⟩], profile := .shrink }
#guard (Core.validate fixture).toBool
#guard (GIR.validate (lower fixture)).toBool

private def joined : Core.Module :=
  let owner := Ty.growshrink (.int .i64)
  let loaded := Expr.read (.deref (.read (.var 0)))
  { fixture with impls := fixture.impls.modify 1 fun impl =>
    { impl with body := .mk 0 [.letS 1 (.arrLit owner []) 0,
      .assignWhole (.var 1) (.arrLit owner [.len (.val (.ifE (.bool true)
        (.mk 1 [] (some loaded)) (.mk 2 [] (some loaded))))]) 0] none } }

private def stored : Core.Module :=
  let owner := Ty.growshrink (.int .i64)
  { fixture with
    impls := fixture.impls.modify 1 fun impl => { impl with
      vars := impl.vars.push ⟨"local_slice", .slice .readOnly (.int .i64), .immutable, 1, 0⟩,
      body := .mk 0 [.letS 1 (.arrLit owner []) 0,
        .assignWhole (.var 1) (.blockE (.mk 1 [.letS 2 (.read (.deref (.read (.var 0)))) 0]
          (some (.arrLit owner [.len (.val (.read (.var 2)))])))) 0] none },
    contexts := fixture.contexts.modify 1 fun context =>
      { context with varRoots := context.varRoots ++ [(2, [])] } }

private def missing : Core.Module :=
  { fixture with contexts := fixture.contexts.modify 1 fun context => { context with contentRoots := [] } }

private def rejectsV050 (input : GIR.Module) : Bool :=
  match GIR.validate input with | .ok () => false | .error failure => failure.code == .v050

#guard (Core.validate joined).toBool
#guard (GIR.validate (lower joined)).toBool
#guard (Core.validate stored).toBool
#guard (GIR.validate (lower stored)).toBool
#guard !(Core.validate missing).toBool
#guard rejectsV050 (lower missing)

private def ownerTy : Ty := .growshrink (.int .i64)
private def sliceTy : Ty := .slice .readOnly (.int .i64)
private def mutableHolder : Ty := .ref .mutable sliceTy
private def emptyMain : GIR.Func :=
  { name := "main", params := [], results := [], slots := #[], scopes := #[none],
    blocks := #[⟨[], [.term (.ret [] (some 0))]⟩], summary := .unknown, org := none }
private def ownerGlobal : GIR.Global :=
  { name := "owner", ty := ownerTy, kind := .mutable, org := 0,
    init := { emptyMain with
      name := "init", results := [ownerTy],
      blocks := #[⟨[], [.def 0 (.arrLit ownerTy []), .term (.ret [0] (some 0))]⟩] } }
private def rawModule (receiver : GIR.Func) (extra : Array GIR.Func := #[]) : GIR.Module :=
  { files := #["replacement-empty-content"], globals := #[ownerGlobal],
    funcs := #[emptyMain, receiver] ++ extra, entry := 0,
    origins := #[⟨0, 1, "statement"⟩], profile := .shrink }
private def rawReceiver (aliased called knownSummary emptyStored : Bool) : GIR.Module :=
  let reference : Ty := if aliased then .ref .readOnly sliceTy else mutableHolder
  let address := if aliased then 8 else 0
  let write : GIR.Inst := if called then .def (if aliased then 9 else 8) (.call 2 [address, 7] (some 0)) else .eff (.store address 7 (some 0))
  let receiver : GIR.Func :=
    { name := "replace", params := [reference, sliceTy] ++ (if aliased then [mutableHolder] else []),
      results := [], slots := #[], scopes := #[none], summary := .unknown, org := none,
      roots := { params := #[(0, [.param 0]), (1, if emptyStored then [] else [.global 0])] ++
        (if aliased then #[(2, [.param 2])] else #[]), contents := #[(0, [])] },
      blocks := #[⟨[(0, .data reference), (7, .data sliceTy)] ++
        (if aliased then [(8, .data mutableHolder)] else []),
        [.def 1 (.arrLit ownerTy []), write, .def 2 (.globalAddr 0), .def 3 (.load 0),
          .eff (.clear 2 (some 0)), .def 4 (.sliceView 3), .def 5 (.viewLen 4),
          .def 6 (.arrLit ownerTy [5]), .eff (.replace 2 6 (some 0)), .term (.ret [] (some 0))]⟩] }
  let callee : GIR.Func :=
    { emptyMain with
      name := "change_contents", params := [mutableHolder, sliceTy],
      roots := { params := #[(0, [.param 0]), (1, [.param 1])] },
      summary := if knownSummary then .known ⟨[], [.param 0], [], [], [.param 0], false, false⟩ else .unknown,
      blocks := #[⟨[(0, .data mutableHolder), (1, .data sliceTy)],
        [.eff (.store 0 1 (some 0)), .term (.ret [] (some 0))]⟩] }
  rawModule receiver (if called then #[callee] else #[])

#guard rejectsV050 (rawReceiver false false false false) == false
#guard match GIR.validate (rawReceiver false false false false) with | .error e => e.code == .v060 | _ => false
#guard match GIR.validate (rawReceiver true false false false) with | .error e => e.code == .v060 | _ => false
#guard match GIR.validate (rawReceiver false true false false) with | .error e => e.code == .v060 | _ => false
#guard match GIR.validate (rawReceiver true true false false) with | .error e => e.code == .v060 | _ => false
#guard match GIR.validate (rawReceiver false true true false) with | .error e => e.code == .v060 | _ => false
#guard match GIR.validate (rawReceiver true true true false) with | .error e => e.code == .v060 | _ => false
#guard (GIR.validate (rawReceiver false false false true)).toBool
#guard (GIR.validate (rawReceiver true false false true)).toBool
#guard match GIR.validate (rawReceiver false true true true) with | .error e => e.code == .v060 | _ => false
#guard match GIR.validate (rawReceiver true true true true) with | .error e => e.code == .v060 | _ => false

private def globalMutation (knownSummary : Bool) : GIR.Module :=
  let header : GIR.Global :=
    { name := "header", ty := sliceTy, kind := .mutable, org := 0,
      init := { emptyMain with
        name := "header_init", results := [sliceTy], roots := { results := #[[.global 0]] },
        blocks := #[⟨[], [.def 0 (.globalAddr 0), .def 1 (.snapshot .owner 0),
          .def 2 (.viewSlice .readOnly 1 .omitted .omitted (some 0)), .term (.ret [2] (some 0))]⟩] } }
  let callee : GIR.Func :=
    { emptyMain with
      name := "change_global", summary := if knownSummary then
        .known ⟨[.global 0], [.global 1], [], [], [], false, false⟩ else .unknown,
      blocks := #[⟨[], [.def 0 (.globalAddr 0), .def 1 (.snapshot .owner 0),
        .def 2 (.viewSlice .readOnly 1 .omitted .omitted (some 0)), .def 3 (.globalAddr 1),
        .eff (.store 3 2 (some 0)), .term (.ret [] (some 0))]⟩] }
  let receiver : GIR.Func :=
    { emptyMain with
      name := "replace", params := [.ref .readOnly sliceTy],
      roots := { params := #[(0, [.global 1])], contents := #[(0, [])] },
      blocks := #[⟨[(0, .data (.ref .readOnly sliceTy))],
        [.def 1 (.call 2 [] (some 0)), .def 2 (.globalAddr 0), .def 3 (.load 0),
          .eff (.clear 2 (some 0)), .def 4 (.sliceView 3), .def 5 (.viewLen 4),
          .def 6 (.arrLit ownerTy [5]), .eff (.replace 2 6 (some 0)), .term (.ret [] (some 0))]⟩] }
  { rawModule receiver #[callee] with globals := #[ownerGlobal, header] }

#guard match GIR.validate (globalMutation false) with | .error e => e.code == .v060 | _ => false
#guard match GIR.validate (globalMutation true) with | .error e => e.code == .v060 | _ => false

private def globalMutationWithEmptyArgument (knownSummary : Bool) : GIR.Module :=
  let input := globalMutation knownSummary
  { input with funcs := input.funcs.modify 1 (fun receiver =>
      { receiver with
        params := receiver.params ++ [sliceTy],
        roots := { receiver.roots with params := receiver.roots.params.push (1, []) },
        blocks := receiver.blocks.modify 0 fun block =>
          { block with
            params := block.params ++ [(7, .data sliceTy)],
            insts := block.insts.map fun
              | .def value (.call fn _ origin) => .def value (.call fn [7] origin)
              | inst => inst } }) |>.modify 2 fun callee =>
      { callee with
        params := [sliceTy], roots := { params := #[(0, [])] },
        blocks := callee.blocks.modify 0 fun block => { block with params := [(4, .data sliceTy)] } } }

#guard match GIR.validate (globalMutationWithEmptyArgument false) with | .error e => e.code == .v060 | _ => false
#guard match GIR.validate (globalMutationWithEmptyArgument true) with | .error e => e.code == .v060 | _ => false

private def globalMutationThroughChain : GIR.Module :=
  let input := globalMutation false
  let wrapper : GIR.Func :=
    { emptyMain with
      name := "mutating_wrapper", blocks := #[⟨[], [.def 0 (.call 2 [] (some 0)), .term (.ret [] (some 0))]⟩] }
  { input with funcs := (input.funcs.modify 1 fun receiver =>
      { receiver with blocks := receiver.blocks.modify 0 fun block =>
        { block with insts := block.insts.map fun
          | .def value (.call _ args origin) => .def value (.call 3 args origin)
          | inst => inst } }).push wrapper }
#guard match GIR.validate globalMutationThroughChain with | .error e => e.code == .v060 | _ => false

private def changedLocalContents (knownSummary : Bool) : GIR.Module :=
  let receiver : GIR.Func :=
    { emptyMain with
      name := "replace_local_copy", params := [.ref .readOnly sliceTy, sliceTy, sliceTy],
      slots := #[⟨sliceTy, .mutable, 0, 0⟩],
      roots := { params := #[(0, [.param 0]), (1, [.global 0]), (2, [])], contents := #[(0, [])] },
      blocks := #[⟨[(0, .data (.ref .readOnly sliceTy)), (7, .data sliceTy), (8, .data sliceTy)],
        [.eff (.enter 0), .def 1 (.arrLit ownerTy []), .def 2 (.globalAddr 0), .def 3 (.load 0),
          .eff (.slotInit 0 3 (some 0)), .def 9 (.slotAddr 0), .def 10 (.call 2 [9, 7, 8] (some 0)),
          .eff (.clear 2 (some 0)), .def 11 (.load 9), .def 4 (.sliceView 11), .def 5 (.viewLen 4),
          .def 6 (.arrLit ownerTy [5]), .eff (.replace 2 6 (some 0)),
          .eff (.leave 0), .term (.ret [] (some 0))]⟩] }
  let callee : GIR.Func :=
    { emptyMain with
      name := "mutate_local_copy", params := [mutableHolder, sliceTy, sliceTy],
      roots := { params := #[(0, [.param 0]), (1, [.param 1]), (2, [.param 2])] },
      summary := if knownSummary then .known ⟨[], [.param 0], [], [], [.param 0], false, false⟩ else .unknown,
      blocks := #[⟨[(0, .data mutableHolder), (1, .data sliceTy), (2, .data sliceTy)],
        [.eff (.store 0 1 (some 0)), .term (.ret [] (some 0))]⟩] }
  rawModule receiver #[callee]
#guard match GIR.validate (changedLocalContents false) with | .error e => e.code == .v060 | _ => false
#guard match GIR.validate (changedLocalContents true) with | .error e => e.code == .v060 | _ => false

private def unchangedLocalContents (knownSummary : Bool) : GIR.Module :=
  let input := changedLocalContents knownSummary
  { input with funcs := input.funcs.modify 2 fun callee =>
    { callee with
      summary := if knownSummary then .known ⟨[], [], [], [], [], false, false⟩ else .unknown,
      blocks := callee.blocks.map fun block => { block with insts := [.term (.ret [] (some 0))] } } }
#guard (GIR.validate (unchangedLocalContents false)).toBool
#guard (GIR.validate (unchangedLocalContents true)).toBool

private def specializedGlobalMutation (localArgument : Bool) : GIR.Module :=
  let input := globalMutationWithEmptyArgument true
  { input with funcs := input.funcs.modify 2 (fun callee =>
      { callee with
        roots := { params := #[(0, if localArgument then [.param 0, .global 1] else [.global 1])] },
        summary := .known ⟨[.global 0], [.param 0], [], [], [], false, false⟩ }) |>.modify 1 fun receiver =>
      if !localArgument then receiver else
        { receiver with
          slots := #[⟨ownerTy, .mutable, 0, 0⟩],
          blocks := receiver.blocks.map fun block =>
            { block with insts := [.eff (.enter 0), .def 8 (.arrLit ownerTy []), .eff (.slotInit 0 8 (some 0)),
                .def 9 (.slotAddr 0), .def 10 (.snapshot .owner 9),
                .def 11 (.viewSlice .readOnly 10 .omitted .omitted (some 0))] ++
              block.insts.flatMap fun
                | .def value (.call fn _ origin) => [.def value (.call fn [11] origin)]
                | .term (.ret values origin) => [.eff (.leave 0), .term (.ret values origin)]
                | inst => [inst] } } }
#guard match GIR.validate (specializedGlobalMutation false) with | .error e => e.code == .v060 | _ => false
#guard match GIR.validate (specializedGlobalMutation true) with | .error e => e.code == .v060 | _ => false

private def staleLocalContents (emptyInitial : Bool) : GIR.Module :=
  let input := changedLocalContents true
  { input with
    globals := input.globals.push { ownerGlobal with name := "unrelated_owner" },
    funcs := input.funcs.modify 1 fun receiver =>
      { receiver with
        params := receiver.params ++ [sliceTy],
        roots := { receiver.roots with params := receiver.roots.params.push (3, if emptyInitial then [] else [.global 1]) },
        blocks := receiver.blocks.modify 0 fun block =>
          { block with
            params := block.params ++ [(12, .data sliceTy)],
            insts := block.insts.map fun
              | .eff (.slotInit slot _ origin) => .eff (.slotInit slot 12 origin)
              | inst => inst } } }

#guard match GIR.validate (staleLocalContents true) with | .error e => e.code == .v060 | _ => false
#guard match GIR.validate (staleLocalContents false) with | .error e => e.code == .v060 | _ => false

end Goose.Lower.Validation.ReplacementEmptyContentChecks
