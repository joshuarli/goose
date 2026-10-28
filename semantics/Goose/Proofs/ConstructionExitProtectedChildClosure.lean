import Goose.Proofs.ConstructionExitAbandonUnique
import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsCleanupAncestry

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

private theorem ancestry_fuel_stable (state : ConstructionState) (ordered : DestinationOwnersOrdered state)
    (ancestor first second id : Nat) (firstBound : id < first) (secondBound : id < second) :
    ancestryWalk state.destinations ancestor first id = ancestryWalk state.destinations ancestor second id := by
  induction first generalizing second id with
  | zero => omega
  | succ first ih =>
    cases second with
    | zero => omega
    | succ second =>
      simp only [ancestryWalk]
      split
      · rfl
      · cases found : state.destinations[id]? with
        | none => rfl
        | some row =>
          simp only
          cases use : row.use with
          | receiver => rfl
          | child parent | replacement parent =>
            simp only
            have earlier : parent < id := by simpa only [use] using ordered id row found
            exact ih second parent (Nat.lt_of_lt_of_le earlier (Nat.le_of_lt_succ firstBound))
              (Nat.lt_of_lt_of_le earlier (Nat.le_of_lt_succ secondBound))

theorem destinationDescendant_child (state : ConstructionState) (ordered : DestinationOwnersOrdered state)
    (ancestor parent id : Nat) (row : PendingDestination)
    (present : state.destinations[id]? = some row) (use : row.use = .child parent)
    (parentDescendant : destinationDescendant state.destinations ancestor parent = true) :
    destinationDescendant state.destinations ancestor id = true := by
  have idInside := (Array.getElem?_eq_some_iff.mp present).1
  have parentEarlier : parent < id := by simpa only [use] using ordered id row present
  rw [destinationDescendant_walk] at parentDescendant ⊢
  cases sizeEq : state.destinations.size with
  | zero => omega
  | succ size =>
    rw [sizeEq] at idInside parentDescendant
    simp only [ancestryWalk]
    by_cases same : id = ancestor
    · simp [same]
    · simp only [beq_iff_eq, same, ↓reduceIte, present, use]
      have enough : parent < size := by omega
      have stable := ancestry_fuel_stable state ordered ancestor size (size + 1) parent enough (by omega)
      rw [stable]
      exact parentDescendant

theorem protectedRows_active_child_closed (state : ConstructionState) (ordered : DestinationOwnersOrdered state)
    (indexed : DestinationCapabilitiesIndexed state) (ancestor replacement parent id : Nat)
    (owner row replacementRow : PendingDestination)
    (ownerMember : owner ∈ protectedRows state ancestor replacement) (ownerId : owner.capability.id = parent)
    (present : state.destinations[id]? = some row) (use : row.use = .child parent) (active : activeRow row = true)
    (replacementFound : state.destinations[replacement]? = some replacementRow)
    (replacementUse : ∃ superseded, replacementRow.use = .replacement superseded) :
    row ∈ protectedRows state ancestor replacement := by
  have ownerDescendant := ((protectedRows_exact_selection state ancestor replacement owner).mp ownerMember).2.2.1
  have descendant : destinationDescendant state.destinations ancestor id = true :=
    destinationDescendant_child state ordered ancestor parent id row present use (by simpa only [ownerId] using ownerDescendant)
  have correct := indexed id row present
  have distinct : id ≠ replacement := by
    intro equal
    rw [equal] at present
    have same := Option.some.inj (replacementFound.symm.trans present)
    subst row
    obtain ⟨superseded, replacementUse⟩ := replacementUse
    rw [use] at replacementUse
    cases replacementUse
  apply (protectedRows_exact_selection state ancestor replacement row).mpr
  refine ⟨Array.mem_toList_iff.mpr (Array.mem_iff_getElem?.mpr ⟨id, present⟩), ?_, ?_, active⟩
  · simpa only [correct] using distinct
  · simpa only [correct] using descendant

theorem protectedExitDiscarded_replacement_use (state : ConstructionState) (ancestor replacement : Nat)
    (rows : List PendingDestination) (checked : protectedExitDiscarded state ancestor replacement = .ok rows) :
    ∃ row superseded count, state.destinations[replacement]? = some row ∧
      row.use = .replacement superseded ∧ row.progress = .built count := by
  simp only [protectedExitDiscarded, bind, pure, Except.bind, Except.pure] at checked
  cases present : state.destinations[replacement]? with
  | none => simp [present] at checked
  | some row =>
    simp only [present] at checked
    cases use : row.use <;> cases progress : row.progress <;>
      simp only [use, progress, Except.bind, Except.pure] at checked <;>
      try contradiction
    all_goals exact ⟨row, _, _, rfl, use, progress⟩

theorem abandonPreservingExit_preserves_blocked_children (before after : ConstructionState)
    (ancestor replacement : Nat) (indexed : DestinationCapabilitiesIndexed before)
    (ordered : DestinationOwnersOrdered before) (valid : ActiveChildParentBlocked before)
    (executed : abandonPreservingExit ancestor replacement before = .ok () after) :
    ActiveChildParentBlocked after := by
  classical
  have checked : ∃ rows, protectedExitDiscarded before ancestor replacement = .ok rows := by
    simp only [abandonPreservingExit, ConstructionM.get, bind] at executed
    cases result : protectedExitDiscarded before ancestor replacement with
    | error fault => simp [result, ConstructionM.fail] at executed
    | ok rows => exact ⟨rows, rfl⟩
  obtain ⟨checkedRows, checkedResult⟩ := checked
  obtain ⟨replacementRow, superseded, count, replacementFound, replacementUse, replacementBuilt⟩ :=
    protectedExitDiscarded_replacement_use before ancestor replacement checkedRows checkedResult
  have exactResult := abandonPreservingExit_exact before ancestor replacement indexed ⟨checkedRows, checkedResult⟩
  have same := (ConstructionResult.ok.inj (exactResult.symm.trans executed)).2
  rw [← same]
  let rows := protectedRows before ancestor replacement
  have bounded := (protectedRows_indexed before ancestor replacement indexed).1
  have distinct := (protectedRows_indexed before ancestor replacement indexed).2
  intro id row owner found use active
  have original := abandonRows_active_source before rows bounded distinct id row found active
  obtain ⟨ownerRow, ownerFound, ownerPhase⟩ := valid id row owner original use active
  by_cases removed : ∃ selected ∈ rows, selected.capability.id = owner
  · obtain ⟨selected, selectedMember, selectedId⟩ := removed
    have childMember : row ∈ rows := protectedRows_active_child_closed before ordered indexed ancestor replacement owner id
      selected row replacementRow selectedMember selectedId original use active replacementFound ⟨superseded, replacementUse⟩
    have abandoned := abandonRowsState_inside rows before bounded distinct row childMember
    have correct := indexed id row original
    rw [correct] at abandoned
    have equal := Option.some.inj (abandoned.symm.trans found)
    have phase := congrArg PendingDestination.progress equal
    have inactive : activeRow row = false := by
      cases progress : row.progress <;> simp_all [activeRow]
    rw [inactive] at active
    cases active
  · have outside : ∀ selected ∈ rows, selected.capability.id ≠ owner := by
      intro selected member equal
      exact removed ⟨selected, member, equal⟩
    exact ⟨ownerRow, by rw [abandonRowsState_outside rows before owner outside]; exact ownerFound, ownerPhase⟩

#print axioms abandonPreservingExit_preserves_blocked_children
#print axioms protectedExitDiscarded_replacement_use
#print axioms destinationDescendant_child
#print axioms protectedRows_active_child_closed

end Goose.Proofs.ConstructionAcceptedExecution
