import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsCleanupRows

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

def protectedCleanupRewireState (state : ConstructionState) (root final : DestinationId)
    (landed : PendingDestination) (parentUpdate : Option (DestinationId × PendingDestination)) : ConstructionState :=
  let cleaned := abandonRowsState (protectedRows state root final) state
  let destinations := cleaned.destinations.set! final landed
  {cleaned with destinations := match parentUpdate with
    | none => destinations
    | some (id, row) => destinations.set! id row}

def ProtectedRewireParent (state : ConstructionState) (root : DestinationId)
    (update : Option (DestinationId × PendingDestination)) : Prop :=
  ∀ id row, update = some (id, row) → ∃ original,
    state.destinations[id]? = some original ∧ row.use = original.use ∧ id < root

theorem protectedCleanupRewire_reads (state : ConstructionState) (root final : DestinationId)
    (landed : PendingDestination) (update : Option (DestinationId × PendingDestination))
    (valid : DestinationLifecycleInvariant state) (inside : final < state.destinations.size)
    (earlier : root < final) (parents : ProtectedRewireParent state root update) :
    OwnershipUsesBackExcept state (protectedCleanupRewireState state root final landed update) final ∧
      (protectedCleanupRewireState state root final landed update).destinations[final]? = some landed := by
  let rows := protectedRows state root final
  let cleaned := abandonRowsState rows state
  have size : cleaned.destinations.size = state.destinations.size := (abandonRowsState_frame rows state).2.2.1
  have current := protectedRows_current state root final valid.2.1
  have unique := (protectedRows_indexed state root final valid.2.1).2
  have lookup (id : DestinationId) (row : PendingDestination)
      (present : cleaned.destinations[id]? = some row) :
      ∃ original, state.destinations[id]? = some original ∧ original.use = row.use :=
    abandonRowsState_use_lookup rows state current unique id row present
  have finalInside : final < cleaned.destinations.size := by simpa only [size] using inside
  cases update with
  | none =>
      refine ⟨?_, ?_⟩
      · intro id row present different
        apply lookup id row
        simpa only [protectedCleanupRewireState, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_ne (Ne.symm different)] using present
      · exact Array.getElem?_setIfInBounds_self_of_lt finalInside
  | some pair =>
      obtain ⟨parent, updated⟩ := pair
      obtain ⟨originalParent, parentPresent, parentUse, parentEarlier⟩ := parents parent updated rfl
      have parentInside : parent < (cleaned.destinations.set! final landed).size := by
        simpa only [Array.size_set!, size] using (Array.getElem?_eq_some_iff.mp parentPresent).1
      have different : parent ≠ final := Nat.ne_of_lt (Nat.lt_trans parentEarlier earlier)
      refine ⟨?_, ?_⟩
      · intro id row present notFinal
        by_cases same : parent = id
        · subst id
          have stored : (protectedCleanupRewireState state root final landed (some (parent, updated))).destinations[parent]? = some updated :=
            Array.getElem?_setIfInBounds_self_of_lt parentInside
          have equal : updated = row := Option.some.inj (stored.symm.trans present)
          subst row
          exact ⟨originalParent, parentPresent, parentUse.symm⟩
        · apply lookup id row
          simpa only [protectedCleanupRewireState, Array.set!_eq_setIfInBounds,
            Array.getElem?_setIfInBounds_ne same, Array.getElem?_setIfInBounds_ne (Ne.symm notFinal)] using present
      · simpa only [protectedCleanupRewireState, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_ne different] using
            (Array.getElem?_setIfInBounds_self_of_lt finalInside :
              ((cleaned.destinations).set! final landed)[final]? = some landed)

theorem protectedCleanupRewire_ordered (state : ConstructionState) (root final : DestinationId)
    (landed : PendingDestination) (update : Option (DestinationId × PendingDestination))
    (valid : DestinationLifecycleInvariant state) (inside : final < state.destinations.size)
    (earlier : root < final) (parents : ProtectedRewireParent state root update)
    (owner : match landed.use with | .receiver => True | .child id | .replacement id => id < final) :
    DestinationOwnersOrdered (protectedCleanupRewireState state root final landed update) := by
  obtain ⟨uses, present⟩ := protectedCleanupRewire_reads state root final landed update valid inside earlier parents
  intro id row found
  by_cases same : id = final
  · subst id
    cases Option.some.inj (found.symm.trans present)
    exact owner
  · obtain ⟨original, originalPresent, originalUse⟩ := uses id row found same
    simpa only [DestinationOwnersOrdered, originalUse] using valid.2.2.2 id original originalPresent

theorem protectedCleanup_rewire_unsupported (state : ConstructionState) (root final : DestinationId)
    (landed : PendingDestination) (update : Option (DestinationId × PendingDestination))
    (valid : DestinationLifecycleInvariant state) (inside : final < state.destinations.size)
    (earlier : root < final) (parents : ProtectedRewireParent state root update)
    (owner : match landed.use with | .receiver => True | .child id | .replacement id => id < final)
    (outside : ∀ parent, landed.use = .replacement parent → parent < root) :
    ¬ ReplacementSupported (protectedCleanupRewireState state root final landed update) root := by
  intro supported
  let after := protectedCleanupRewireState state root final landed update
  have ordered := protectedCleanupRewire_ordered state root final landed update valid inside earlier parents owner
  obtain ⟨uses, finalPresent⟩ := protectedCleanupRewire_reads state root final landed update valid inside earlier parents
  obtain ⟨leaf, row, present, active, path⟩ := replacementSupported_active_path after root supported
  have different := path.ne_rewired ordered landed finalPresent outside (Nat.ne_of_lt earlier)
  have priorPath := path.before_rewire ordered landed finalPresent outside uses
  obtain ⟨original, originalPresent, _⟩ := uses leaf row present different
  have descendant := priorPath.descendant valid.2.2.2 (Array.getElem?_eq_some_iff.mp originalPresent).1
  have cleanedPresent : (abandonRowsState (protectedRows state root final) state).destinations[leaf]? = some row := by
    cases update with
    | none =>
        simpa only [after, protectedCleanupRewireState, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_ne (Ne.symm different)] using present
    | some pair =>
        obtain ⟨parent, updated⟩ := pair
        obtain ⟨originalParent, parentPresent, parentUse, parentEarlier⟩ := parents parent updated rfl
        have notParent : parent ≠ leaf := Nat.ne_of_lt (Nat.lt_of_lt_of_le parentEarlier (path.le ordered))
        simpa only [after, protectedCleanupRewireState, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_ne notParent,
          Array.getElem?_setIfInBounds_ne (Ne.symm different)] using present
  have inactive := protectedCleanup_inactive state root final leaf original row valid.2.1 originalPresent
    descendant different cleanedPresent
  exact Bool.noConfusion (active.symm.trans inactive)

end Goose.Proofs.ConstructionExecutionOwnership
