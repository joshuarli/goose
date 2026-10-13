import Goose.Core.Sound.CallPreservation
namespace Goose.Core.Sound.CallBoundaryPrecisionChecks.LimitedGhost
open Goose.Core

/-- A limited-reference annotation may include an unrelated grow root. A
forwarded reference keeps that annotation for content typing, while its declared
limited slot grants no grow-header authority. -/
def module : Module :=
  let owner := Ty.growshrink .bool
  let limited := Ty.limited .bool 1
  let slice := Ty.slice .mutable .bool
  let summary (ts : List Target) : SummaryAnn := .known ⟨ts, ts, [], ts, [], true, true⟩
  let main : Impl := {
    name := "main", params := #[], results := #[]
    vars := #[⟨"reference", .ref .readOnly limited, .immutable, 0, 0⟩]
    body := .mk 0 [
      .letS 0 (.ref .readOnly (.global 1)) 0,
      .expr (.call 1 [.byRef .readOnly (.deref (.read (.var 0)))] 0) 0,
      .print [.text "ok"] 0] none
    summary := .unknown }
  let prepare : Impl := {
    name := "prepare", params := #[⟨0, .byRef⟩], results := #[]
    vars := #[⟨"limited", .ref .readOnly limited, .immutable, 0, 0⟩,
      ⟨"owner", owner, .mutable, 0, 0⟩,
      ⟨"header", slice, .mutable, 0, 0⟩]
    body := .mk 0 [
      .letS 1 (.arrLit owner [.bool true]) 0,
      .letS 2 (.slice .mutable (.of (.global 0)) .omitted .omitted 0) 0,
      .expr (.call 2 [.byRef .mutable (.var 2), .byRef .mutable (.var 1),
        .byRef .readOnly (.deref (.read (.var 0)))] 0) 0] none
    summary := .known ⟨[.param 0, .global 0], [.param 0, .global 0], [], [.param 0], [], true, true⟩ }
  let middle : Impl := {
    name := "middle", params := #[⟨0, .byRef⟩, ⟨1, .byRef⟩, ⟨2, .byRef⟩], results := #[]
    vars := #[⟨"header", .ref .mutable slice, .immutable, 0, 0⟩,
      ⟨"owner", .ref .mutable owner, .immutable, 0, 0⟩,
      ⟨"limited", .ref .readOnly limited, .immutable, 0, 0⟩,
      ⟨"reference", .ref .mutable owner, .immutable, 0, 0⟩]
    body := .mk 0 [
      .letS 3 (.read (.var 1)) 0,
      .expr (.call 3 [.byRef .mutable (.deref (.read (.var 3)))] 0) 0] none
    summary := summary [.param 1, .param 2] }
  let shrink : Impl := {
    name := "shrink", params := #[⟨0, .byRef⟩], results := #[]
    vars := #[⟨"owner", .ref .mutable owner, .immutable, 0, 0⟩]
    body := .mk 0 [.clear (.deref (.read (.var 0))) 0] none
    summary := summary [.param 0] }
  { files := #["witness.goose"], types := #[]
    globals := #[⟨"backing", owner, .mutable, .arrLit owner [.bool true], 0⟩,
      ⟨"limited", limited, .mutable, .arrLit limited [.bool true], 0⟩]
    impls := #[main, prepare, middle, shrink]
    contexts := #[
      ⟨0, "main", [(0, [.global 0, .global 1])], [], []⟩,
      ⟨1, "prepare", [(0, [.param 0]), (2, [.global 0])], [], []⟩,
      ⟨2, "middle", [(0, [.param 0]), (1, [.param 1]), (2, [.param 2]),
        (3, [.param 1, .param 2])], [], [(0, [.global 0])]⟩,
      ⟨3, "shrink", [(0, [.param 0])], [], []⟩]
    entry := 0, origins := #[⟨0, 1, "stmt"⟩], profile := .shrink }
def shrinkArgument : Arg := .byRef .mutable (.deref (.read (.var 3)))
def middleAccess : AccessEnv := ⟨module, module.impls[2]'(by decide),
  module.contexts[2]'(by decide)⟩
#guard match middleAccess.argRoots shrinkArgument with
  | .ok roots => roots == [.param 1, .param 2]
  | _ => false
#guard match middleAccess.callShrinkOwners 3 [shrinkArgument] with
  | .ok owners => owners == [⟨some (.growshrink .bool), [.param 1]⟩,
      ⟨some (.limited .bool 1), [.param 2]⟩]
  | _ => false
#guard (⟨some (.limited .bool 1), [.param 2]⟩ : DemandOwner).invalidates == false
#guard match DemandNode.expectedPoints module 3 with
  | .ok points => points.any (fun point => point.phase == .mutation &&
      point.shrinkOwners.contains ⟨some (.growshrink .bool), [.param 0]⟩)
  | _ => false
#guard match validate module with
  | .ok _ => true
  | .error _ => false
#guard match runModule 100 ⟨.release, module⟩ St.initial with
  | .ok _ state => state.trace == "ok\n" &&
      match state.store.roots[RootInst.global 0]? with
      | some (.resizable .bool values) => values.size == 1 &&
          match values[0]? with | some (Val.bool true) => true | _ => false
      | _ => false
  | _ => false
end Goose.Core.Sound.CallBoundaryPrecisionChecks.LimitedGhost

namespace Goose.Core.Sound.CallBoundaryPrecisionChecks.Contents
open Goose.Core

/-- A content annotation may name both owner roots even when the owner
argument value points at only one. Returning the other stored slice must remain
accepted, so content-root interpretation cannot use only argument targets. -/
def module : Module :=
  let owner := Ty.growshrink .bool
  let slice := Ty.slice .mutable .bool
  let main : Impl := {
    name := "main", params := #[], results := #[]
    vars := #[⟨"first", owner, .mutable, 0, 0⟩,
      ⟨"second", owner, .mutable, 0, 0⟩,
      ⟨"header", slice, .mutable, 0, 0⟩,
      ⟨"reference", .ref .mutable owner, .immutable, 0, 0⟩]
    body := .mk 0 [
      .letS 0 (.arrLit owner [.bool true]) 0,
      .letS 1 (.arrLit owner [.bool false]) 0,
      .letS 2 (.slice .mutable (.of (.var 1)) .omitted .omitted 0) 0,
      .letS 3 (.ref .mutable (.var 0)) 0,
      .expr (.call 1 [.byRef .mutable (.var 2),
        .byRef .mutable (.deref (.read (.var 3)))] 0) 0,
      .print [.text "ok"] 0] none
    summary := .unknown }
  let returned : Impl := {
    name := "returned", params := #[⟨0, .byRef⟩, ⟨1, .byRef⟩], results := #[slice]
    vars := #[⟨"header", .ref .mutable slice, .immutable, 0, 0⟩,
      ⟨"owner", .ref .mutable owner, .immutable, 0, 0⟩]
    body := .mk 0 [] (some (.read (.deref (.read (.var 0)))))
    summary := .known ⟨[.param 0], [], [], [], [], true, true⟩ }
  { files := #["witness.goose"], types := #[], globals := #[]
    impls := #[main, returned]
    contexts := #[
      ⟨0, "main", [(2, [.local 0, .local 1]), (3, [.local 0, .local 1])], [], []⟩,
      ⟨1, "returned", [(0, [.param 0]), (1, [.param 1])], [[.param 1]], [(0, [.param 1])]⟩]
    entry := 0, origins := #[⟨0, 1, "stmt"⟩], profile := .shrink }
#guard match validate module with
  | .ok _ => true
  | .error _ => false
#guard match runModule 100 ⟨.release, module⟩ St.initial with
  | .ok _ state => state.trace == "ok\n"
  | _ => false
def firstRoot : RootInst := .local 0 0 0
def secondRoot : RootInst := .local 0 0 1
def headerRoot : RootInst := .local 0 0 2
def arguments : List Val := [.ref ⟨headerRoot, []⟩, .ref ⟨firstRoot, []⟩]
def entry : St := { St.initial with
  nextAct := 1
  nextScope := 1
  store := (Store.empty
    |>.introduce firstRoot (.resizable .bool #[.bool true])
    |>.introduce secondRoot (.resizable .bool #[.bool false])
    |>.introduce headerRoot (.slice ⟨secondRoot, []⟩ 0 1)) }
#guard match enterCall 20 ⟨.release, module⟩ 0 1 arguments entry with
  | .ok (.slice location start count) _ =>
      location.root == secondRoot && location.path.isEmpty && start == 0 && count == 1
  | _ => false

example : ¬ Gam noEnv (fun index root => ∃ value,
    arguments[index]? = some value ∧ Targets value root) [.param 1] secondRoot := by
  simp [Gam, RootIn, arguments, Targets, firstRoot, secondRoot]

end Goose.Core.Sound.CallBoundaryPrecisionChecks.Contents
