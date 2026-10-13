import Goose.Core.Validate
import Goose.Core.Run

namespace Goose.Core.ForeachChecks

open Goose.Core

private def intTy : Ty := .int .i64
private def limitedTy : Ty := .limited intTy 2
private def growTy : Ty := .grow intTy

private def unrelatedGlobal : Global := {
  name := "unrelated"
  ty := growTy
  kind := .mutable
  init := .arrLit growTy []
  org := 0 }

private def mainImpl : Impl := {
  name := "main"
  params := #[]
  results := #[]
  vars := #[⟨"bounded", limitedTy, .mutable, 0, 0⟩]
  body := .mk 0 [
    .letS 0 (.arrLit limitedTy [.lit .i64 1]) 0,
    .expr (.call 1 [.byRef .mutable (.var 0)] 0) 0] none
  summary := .unknown }

private def iterateImpl : Impl := {
  name := "iterate"
  params := #[⟨0, .byRef⟩]
  results := #[]
  vars := #[
    ⟨"values", .ref .mutable limitedTy, .immutable, 0, 0⟩,
    ⟨"element", intTy, .immutable, 1, 0⟩]
  body := .mk 0 [
    .forEach 1 none (.of (.deref (.read (.var 0)))) false
      (.mk 1 [ .expr (.call 2 [] 0) 0 ] none) 0] none
  summary := .unknown }

private def opaqueMutator : Impl := {
  name := "opaque_mutator"
  params := #[]
  results := #[]
  vars := #[]
  body := .mk 0 [ .clear (.global 0) 0 ] none
  summary := .unknown }

/-- This checked-Core module is accepted: `limited` keeps the by-value loop
element outside shrink-sensitive alias tracking while the unknown call may
still reach the unrelated global. -/
private def limitedModule : Module := {
  files := #["foreach_limited_audit.goose"]
  types := #[intTy, limitedTy, growTy]
  structs := #[]
  globals := #[unrelatedGlobal]
  impls := #[mainImpl, iterateImpl, opaqueMutator]
  contexts := #[
    ⟨0, "main()", [], [], []⟩,
    ⟨1, "iterate()", [(0, [.param 0])], [], []⟩,
    ⟨2, "opaque_mutator()", [], [], []⟩]
  entry := 0
  origins := #[⟨0, 1, "expr"⟩]
  profile := .shrink }

private def growshrinkTy : Ty := .growshrink intTy
private def sliceTy : Ty := .slice .mutable intTy

private def growshrinkGlobal : Global := {
  name := "source"
  ty := growshrinkTy
  kind := .mutable
  init := .arrLit growshrinkTy [.lit .i64 1]
  org := 0 }

private def growshrinkMainImpl : Impl := {
  name := "main"
  params := #[]
  results := #[]
  vars := #[
    ⟨"run", sliceTy, .immutable, 0, 0⟩,
    ⟨"element", intTy, .immutable, 1, 0⟩]
  body := .mk 0 [
    .letS 0 (.slice .mutable (.of (.global 0)) .omitted .omitted 0) 0,
    .forEach 1 none (.val (.read (.var 0))) false
      (.mk 1 [ .expr (.call 1 [] 0) 0 ] none) 0] none
  summary := .unknown }

/-- Here the same destructive call can reach the growshrink source being
iterated, so the loop must be rejected. -/
private def growshrinkModule : Module := {
  files := #["foreach_limited_audit.goose"]
  types := #[intTy, growshrinkTy, sliceTy]
  structs := #[]
  globals := #[growshrinkGlobal]
  impls := #[growshrinkMainImpl, opaqueMutator]
  contexts := #[
    ⟨0, "main()", [(0, [.global 0])], [], []⟩,
    ⟨1, "opaque_mutator()", [], [], []⟩]
  entry := 0
  origins := #[⟨0, 1, "expr"⟩]
  profile := .shrink }

#guard match validate limitedModule with
  | .ok _ => true
  | .error _ => false

#guard rootsMayOverlap (.param 0) (.global 0)

#guard match runModule 100 ⟨.release, limitedModule⟩ St.initial with
  | .ok _ state => state.trace == ""
  | _ => false

#eval match validate growshrinkModule with
  | .error rejection => s!"{rejection.rule.tag}: {rejection.message}"
  | .ok _ => "accepted"

#guard match validate growshrinkModule with
  | .error rejection =>
      rejection.rule.tag == "V-SHRINK" && rejection.message.startsWith "shrink conflicts"
  | .ok _ => false

end Goose.Core.ForeachChecks
