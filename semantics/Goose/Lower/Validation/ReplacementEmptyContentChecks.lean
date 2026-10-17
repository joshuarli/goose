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
#guard (GIR.validate (rawReceiver false true true true)).toBool
#guard (GIR.validate (rawReceiver true true true true)).toBool

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

end Goose.Lower.Validation.ReplacementEmptyContentChecks
