import Goose.Core.Sound.CallPreservation

namespace Goose.Core.Sound.CallClassificationChecks
open Goose.Core Goose.Proofs.Memory

def module : Module :=
  let owner := Ty.growshrink .bool
  let slice := Ty.slice .mutable .bool
  let array := Ty.arr .bool 1
  let main : Impl := {
    name := "main", params := #[], results := #[]
    vars := #[⟨"array", array, .mutable, 0, 0⟩,
      ⟨"header", slice, .mutable, 0, 0⟩]
    body := .mk 0 [
      .letS 0 (.arrLit array [.bool true]) 0,
      .letS 1 (.slice .mutable (.of (.var 0)) .omitted .omitted 0) 0,
      .expr (.call 2 [.byVal (.call 1
        [.byRef .mutable (.var 1), .byRef .readOnly (.var 0)] 0)] 0) 0,
      .print [.text "ok"] 0] none
    summary := .unknown }
  let returned : Impl := {
    name := "returnSlice", params := #[⟨0, .byRef⟩, ⟨1, .byRef⟩], results := #[slice]
    vars := #[⟨"header", .ref .mutable slice, .immutable, 0, 0⟩,
      ⟨"array", .ref .readOnly array, .immutable, 0, 0⟩]
    body := .mk 0 [] (some (.read (.deref (.read (.var 0)))))
    summary := .known ⟨[.param 0, .param 1], [], [], [], [], false, false⟩ }
  let consumer : Impl := {
    name := "consume", params := #[⟨0, .byValue⟩], results := #[]
    vars := #[⟨"slice", slice, .immutable, 0, 0⟩]
    body := .mk 0 [.clear (.global 0) 0] none
    summary := .known ⟨[.global 0, .param 0], [], [], [.global 0], [], false, false⟩ }
  { files := #["witness.goose"], types := #[]
    globals := #[⟨"unrelated", owner, .mutable, .arrLit owner [.bool true], 0⟩]
    impls := #[main, returned, consumer]
    contexts := #[
      ⟨0, "main", [(1, [.local 0])], [], []⟩,
      ⟨1, "returnSlice", [(0, [.param 0]), (1, [.param 1])],
        [[.param 0, .param 1]], [(0, [.param 1])]⟩,
      ⟨2, "consume", [(0, [.param 0])], [], []⟩]
    entry := 0, origins := #[⟨0, 1, "expr"⟩], profile := .shrink }

def outerArgument : Arg := .byVal (.call 1
  [.byRef .mutable (.var 1), .byRef .readOnly (.var 0)] 0)
def access : AccessEnv := ⟨module, module.impls[0]'(by decide), module.contexts[0]'(by decide)⟩
#guard match access.argRoots outerArgument with
  | .ok roots => roots == [.local 1, .local 0]
  | _ => false

#guard match validate module with | .ok _ => true | .error _ => false
#guard match runModule 100 ⟨.release, module⟩ St.initial with
  | .ok _ state => state.trace == "ok\n"
  | _ => false


def backingRoot : RootInst := .local 0 0 0
def headerRoot : RootInst := .local 0 0 1
def snapshot : Store :=
  Store.empty
    |>.introduce backingRoot (.fixed #[.bool true])
    |>.introduce headerRoot (.slice ⟨backingRoot, []⟩ 0 1)
def observation : Observation :=
  ⟨fun r T => r = backingRoot ∧ T = .arr .bool 1, fun _ _ => False⟩
def parameters (index : Nat) (r : RootInst) : Prop :=
  index = 0 ∧ (r = headerRoot ∨ r = backingRoot)

example : ClassifiedParameters module parameters (fun _ _ => False) observation snapshot := by
  intro index root parameter
  rcases parameter.2 with rfl | rfl
  · refine Or.inr (Or.inr (Or.inl ⟨.slice ⟨backingRoot, []⟩ 0 1, ?_, trivial⟩))
    simp [snapshot, headerRoot, backingRoot, get_introduce]
  · exact Or.inl ⟨.arr .bool 1, rfl, rfl⟩

example : ¬ ((∃ T, observation.roots headerRoot T) ∨
    (∃ _ : Ty, False) ∨ snapshot.roots[headerRoot]? = none) := by
  simp [observation, headerRoot, backingRoot, snapshot, get_introduce]

end Goose.Core.Sound.CallClassificationChecks
