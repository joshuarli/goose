import Goose.Core.Validate
import Goose.Lower.CoreToGir
import Goose.GIR.Validate

namespace Goose.Lower.Validation.SummaryResultOriginsCounterexample

open Goose.Core

def scalar : Ty := .int .i64

def slice : Ty := .slice .mutable scalar

def receiver : Impl :=
  { name := "content_reference", params := #[⟨0, .byRef⟩, ⟨1, .byRef⟩],
    results := #[.ref .mutable scalar],
    vars := #[⟨"unused", .ref .mutable slice, .immutable, 0, 0⟩,
      ⟨"contents", .ref .mutable slice, .immutable, 0, 0⟩],
    body := .mk 0 [] (some (.ref .mutable (.elem
      (.val (.read (.deref (.read (.var 1))))) (.lit .i64 0) 0))),
    summary := .known { reads := [.param 1], writes := [], grows := [], shrinks := [], rebinds := [], aborts := true, outputs := false } }

def middle : Impl :=
  { name := "forward_content_reference", params := #[⟨0, .byRef⟩],
    results := #[.ref .mutable scalar],
    vars := #[⟨"forwarded", .ref .mutable slice, .immutable, 0, 0⟩,
      ⟨"local", slice, .mutable, 0, 0⟩],
    body := .mk 0 [.letS 1 (.slice .mutable (.of (.global 0)) .omitted .omitted 0) 0]
      (some (.call 3 [.byRef .mutable (.deref (.read (.var 0))), .byRef .mutable (.var 1)] 0)),
    summary := .known { reads := [.global 0], writes := [], grows := [], shrinks := [], rebinds := [], aborts := true, outputs := false } }

def caller : Impl :=
  { name := "slice_parameter", params := #[⟨0, .byValue⟩], results := #[],
    vars := #[⟨"parameter", slice, .mutable, 0, 0⟩],
    body := .mk 0 [.assign (.deref (.call 2 [.byRef .mutable (.var 0)] 0)) (.lit .i64 1) 0] none,
    summary := .known { reads := [.global 0], writes := [.global 0], grows := [], shrinks := [], rebinds := [], aborts := true, outputs := false } }

def entry : Impl :=
  { name := "main", params := #[], results := #[], vars := #[],
    body := .mk 0 [.expr (.call 1 [.byVal (.slice .mutable (.of (.global 0)) .omitted .omitted 0)] 0) 0] none,
    summary := .known { reads := [.global 0], writes := [.global 0], grows := [], shrinks := [], rebinds := [], aborts := true, outputs := false } }

def module : Module :=
  { files := #["result-content-holder.goose"], types := #[],
    globals := #[⟨"data", .arr scalar 1, .mutable, .arrLit (.arr scalar 1) [.lit .i64 0], 0⟩],
    impls := #[entry, caller, middle, receiver],
    contexts := #[⟨0, "main", [], [], []⟩,
      ⟨1, "slice_parameter", [(0, [.global 0])], [], []⟩,
      ⟨2, "forward_content_reference", [(0, [.param 0]), (1, [.param 0, .global 0])], [[.param 0, .global 0]], []⟩,
      ⟨3, "content_reference", [(0, [.param 0]), (1, [.param 1])], [[.param 0, .global 0]],
        [(1, [.param 0, .global 0])]⟩],
    entry := 0, origins := #[⟨0, 1, "expr"⟩] }

def lowered : GIR.Module := Lower.lower module

def valueTypes : Array (Array (Option GIR.VTy)) := lowered.funcs.map (GIR.Func.valueTypes lowered)

def computed : Array (List RootRef) := GIR.resultRoots lowered valueTypes

#guard match Core.validate module with | .ok () => true | .error _ => false

#guard match GIR.validate lowered with | .ok () => true | .error _ => false

#guard RootRef.param 0 ∈ GIR.rootsAt computed 2

#guard (lowered.funcs[2]?).any (fun func => func.roots.contents.isEmpty)

#guard (lowered.funcs[2]?).any (fun func => (func.params[0]?).any Ty.isRefSlice)

#guard (lowered.funcs[2]?).any (fun func => (func.results[0]?).any (fun ty => !ty.isRefSlice))

end Goose.Lower.Validation.SummaryResultOriginsCounterexample
