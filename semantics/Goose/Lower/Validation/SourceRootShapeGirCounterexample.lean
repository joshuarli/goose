import Goose.Lower.Validation.SourceRootShapeCounterexample
import Goose.Lower.CoreToGir
import Goose.GIR.Validate

namespace Goose.Lower.Validation.SourceRootShapeGirCounterexample

open Goose.Core
open SourceRootShapeCounterexample

def callee : Impl :=
  { SourceRootShapeCounterexample.callee with
    summary := .known { reads := [.global 0], writes := [], grows := [], shrinks := [], rebinds := [], aborts := true, outputs := false } }

def caller : Impl :=
  { name := "slice_parameter", params := #[⟨0, .byValue⟩], results := #[],
    vars := #[⟨"view", slice, .mutable, 0, 0⟩],
    body := .mk 0 [.assign (.deref (.call 2 [.byRef .mutable (.var 0)] 0)) (.lit .i64 1) 0] none,
    summary := .known { reads := [.global 0], writes := [.global 0], grows := [], shrinks := [], rebinds := [], aborts := true, outputs := false } }

def entry : Impl :=
  { name := "main", params := #[], results := #[], vars := #[],
    body := .mk 0 [.expr (.call 1
      [.byVal (.slice .mutable (.of (.global 0)) .omitted .omitted 0)] 0) 0] none,
    summary := .known { reads := [.global 0], writes := [.global 0], grows := [], shrinks := [], rebinds := [], aborts := true, outputs := false } }

def module : Module :=
  { SourceRootShapeCounterexample.module with
    impls := #[entry, caller, callee],
    contexts := #[⟨0, "main", [], [], []⟩,
      ⟨1, "slice_parameter", [(0, [.global 0])], [], []⟩,
      ⟨2, "global_reference", [(0, [.param 0])], [[.param 0, .global 0]], [(0, [.global 0])]⟩] }

#guard match Core.validate module with | .ok () => true | .error _ => false

#guard match GIR.validate (Lower.lower module) with | .ok () => true | .error _ => false

def typingEnv : TEnv :=
  { mod := module, impl := some caller, vars := caller.vars, visible := [0], loops := 0,
    inExpr := false, scopes := [0], globalLimit := 1, initializing := none }

def rootsEnv : PEnv := ⟨module, caller, module.contexts[1], [0]⟩

def target : Place := .deref (.call 2 [.byRef .mutable (.var 0)] 0)

theorem target_flat_typed : Core.tyPlace typingEnv target 1 = .ok (⟨scalar, true, true⟩, 1) := by rfl

theorem target_roots : Core.rpPlace rootsEnv target ⟨1, {}⟩ =
    .ok ([.local 0, .global 0], ⟨1, { reads := [.global 0], aborts := true }⟩) := by rfl

theorem local_parameter_is_slice : (caller.vars[0]).ty.isSlice = true := by rfl

end Goose.Lower.Validation.SourceRootShapeGirCounterexample
