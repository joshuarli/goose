import Goose.Core.Validate
import Goose.Lower.CoreToGir
import Goose.GIR.Validate

namespace Goose.Lower.Validation.ContentAnnotationChecks

open Goose.Core

def scalar : Ty := .int .i64

def slice : Ty := .slice .mutable scalar

def callee : Impl :=
  { name := "global_reference", params := #[⟨0, .byRef⟩], results := #[.ref .mutable scalar],
    vars := #[⟨"unused", .ref .mutable slice, .immutable, 0, 0⟩],
    body := .mk 0 [] (some (.ref .mutable (.elem (.of (.global 0)) (.lit .i64 0) 0))),
    summary := .unknown }

def place : Place := .deref (.call 1 [.byRef .mutable (.var 0)] 0)

def caller : Impl :=
  { name := "main", params := #[], results := #[],
    vars := #[⟨"view", slice, .mutable, 0, 0⟩],
    body := .mk 0
      [.letS 0 (.slice .mutable (.of (.global 0)) .omitted .omitted 0) 0,
       .assign place (.lit .i64 1) 0] none,
    summary := .unknown }

def callerContext : Context := ⟨0, "main", [(0, [.global 0])], [], []⟩

def module : Module :=
  { files := #["roots.goose"], types := #[],
    globals := #[⟨"data", .arr scalar 1, .mutable, .arrLit (.arr scalar 1) [.lit .i64 0], 0⟩],
    impls := #[caller, callee],
    contexts := #[callerContext, ⟨1, "global_reference", [(0, [.param 0])], [[.param 0, .global 0]], []⟩],
    entry := 0, origins := #[⟨0, 1, "call"⟩] }

private def rejectsV050 (input : GIR.Module) : Bool :=
  match GIR.validate input with
  | .ok () => false
  | .error rejection => rejection.code == .v050

private def explicitEmpty : Module :=
  { module with contexts := module.contexts.modify 1 fun context =>
    { context with contentRoots := [(0, [])] } }

private def usedMissing : Module :=
  { module with impls := module.impls.modify 1 fun impl =>
    { impl with body := .mk 0 [] (some (.ref .mutable
      (.elem (.val (.read (.deref (.read (.var 0))))) (.lit .i64 0) 0))) } }

private def usedAnnotated : Module :=
  { usedMissing with contexts := usedMissing.contexts.modify 1 fun context =>
    { context with contentRoots := [(0, [.global 0])] } }

#guard (Core.validate module).toBool
#guard (GIR.validate (Lower.lower module)).toBool
#guard !(Core.validate explicitEmpty).toBool
#guard rejectsV050 (Lower.lower explicitEmpty)
#guard !(Core.validate usedMissing).toBool
#guard rejectsV050 (Lower.lower usedMissing)

#guard (Core.validate usedAnnotated).toBool
#guard (GIR.validate (Lower.lower usedAnnotated)).toBool

end Goose.Lower.Validation.ContentAnnotationChecks
