import Goose.Proofs.ConstructionExitBlockedOpenChild

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership

private def capability (id : Nat) : Goose.Core.Destination Goose.Construct.Ty :=
  ⟨id, ⟨.global 0, []⟩, .unit, .unit, .value, 0, 0⟩

private def parent : PendingDestination :=
  ⟨capability 0, .direct 0, .elements, .receiver, .suspended 0 1, 0, 0, none, none⟩

private def chosen : PendingDestination :=
  ⟨capability 1, .direct 0, .elements, .child 0, .built 0, 0, 0, none, none⟩

private def sibling : PendingDestination :=
  ⟨capability 2, .direct 0, .elements, .child 0, .open 0, 0, 0, none, none⟩

private def before : ConstructionState :=
  { ConstructionState.initial with storage := #[⟨ByteArray.empty, 0⟩], destinations := #[parent, chosen, sibling] }

private def after : ConstructionState :=
  { before with
    destinations := #[{ parent with progress := .open 1 }, { chosen with progress := .attached 0 }, sibling]
    events := [.write 0 0] }

private theorem before_blocked : ActiveChildParentBlocked before := by
  intro id row owner found used active
  cases id with
  | zero => simp [before, parent] at found; subst row; simp [parent] at used
  | succ id =>
    cases id with
    | zero =>
      simp [before, chosen] at found
      subst row
      simp [chosen] at used
      subst owner
      exact ⟨parent, by rfl, Or.inl ⟨0, 1, rfl⟩⟩
    | succ id =>
      cases id with
      | zero =>
        simp [before, sibling] at found
        subst row
        simp [sibling] at used
        subst owner
        exact ⟨parent, by rfl, Or.inl ⟨0, 1, rfl⟩⟩
      | succ id => simp [before] at found

private theorem before_ordered : DestinationOwnersOrdered before := by
  intro id row found
  cases id with
  | zero => simp [before, parent] at found; subst row; simp [parent]
  | succ id =>
    cases id with
    | zero => simp [before, chosen] at found; subst row; simp [chosen]
    | succ id =>
      cases id with
      | zero => simp [before, sibling] at found; subst row; simp [sibling]
      | succ id => simp [before] at found

private theorem attach_result : attachChild 0 1 before = .ok () after := by
  have writableParent : destinationCanWrite before 0 = true := by simp [destinationCanWrite, before, parent, chosen, sibling, capability, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.range', List.forIn_cons, List.forIn_nil]
  have writableChild : destinationCanWrite before 1 = true := by simp [destinationCanWrite, before, parent, chosen, sibling, capability, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.range', List.forIn_cons, List.forIn_nil]
  simp only [attachChild, writableDestination_result,
    show before.destinations[0]? = some parent from rfl,
    show before.destinations[1]? = some chosen from rfl,
    writableParent, writableChild, bind, ↓reduceIte]
  simp [parent, chosen, sibling, capability, before, after, ConstructionState.initial, replaceDestination_result, emit_result,
    bind, pure, PendingDestination.storage, DestinationBacking.writeStorage, Array.set!_eq_setIfInBounds]


private theorem after_not_blocked : ¬ ActiveChildParentBlocked after := by
  intro valid
  have blocked := valid 2 sibling 0 (by rfl) (by rfl) (by rfl)
  obtain ⟨owner, present, phase⟩ := blocked
  have same : owner = { parent with progress := .open 1 } := by
    exact Option.some.inj (present.symm.trans (by rfl))
  subst owner
  rcases phase with ⟨count, child, phase⟩ | ⟨count, replacement, phase⟩ <;> cases phase

theorem attachChild_blocked_parent_not_inductive :
    ∃ before after, ActiveChildParentBlocked before ∧ DestinationOwnersOrdered before ∧ attachChild 0 1 before = .ok () after ∧
      ¬ ActiveChildParentBlocked after :=
  ⟨before, after, before_blocked, before_ordered, attach_result, after_not_blocked⟩

#print axioms attachChild_blocked_parent_not_inductive

end Goose.Proofs.ConstructionAcceptedExecution
