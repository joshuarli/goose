import Goose.Core.Validate

namespace Goose.Lower.Validation.SourceRootShapeCounterexample

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

def typingEnv : TEnv :=
  { mod := module, impl := some caller, vars := caller.vars, visible := [0], loops := 0,
    inExpr := false, scopes := [0], globalLimit := 1, initializing := none }

def rootsEnv : PEnv := ⟨module, caller, callerContext, [0]⟩

#guard match Core.validate module with | .ok () => true | .error _ => false

theorem place_typed : Core.tyPlace typingEnv place 1 = .ok (⟨scalar, true, true⟩, 1) := by rfl

theorem place_flat : scalar.flat = true := by rfl

theorem replayed : Core.rpPlace rootsEnv place ⟨1, {}⟩ =
    .ok ([.local 0, .global 0], ⟨1, { unknown := true }⟩) := by rfl

theorem local_holds_slice : (caller.vars[0]).ty.isRefLike = true := by rfl

end Goose.Lower.Validation.SourceRootShapeCounterexample
