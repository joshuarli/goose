import Goose.Proofs.ConstructionExitBlockedParent
import Goose.Proofs.ConstructionExitByteReservationFrame

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem open_replacement_preserves_blocked_children (before after : ConstructionState)
    (incoming selected count : Nat) (receiver : PendingDestination) (storage : ReceivingStorage)
    (present : before.destinations[incoming]? = some receiver) (opened : receiver.progress = .open count)
    (stored : before.storage[receiver.storage]? = some storage)
    (ordered : DestinationOwnersOrdered before) (valid : ActiveChildParentBlocked before)
    (executed : openExitReplacement incoming before = .ok selected after) :
    ActiveChildParentBlocked after := by
  have frame := open_replacement_other_rows before after incoming selected count receiver storage present opened stored executed
  have fresh := open_replacement_fresh before after incoming selected count receiver storage present opened stored executed
  have parent := open_replacement_parent_exact before after incoming selected count receiver present opened executed
  obtain ⟨newParent, replacement, n, newParentFound, newParentPhase, newParentActive, replacementFound, replacementUse⟩ :=
    openExitReplacement_new_parent_active before after incoming selected executed
  have selectedRole : ∀ row, after.destinations[selected]? = some row → row.use = .replacement incoming := by
    intro row found
    have same := Option.some.inj (replacementFound.symm.trans found)
    subst row
    exact replacementUse
  have incomingInside := (Array.getElem?_eq_some_iff.mp present).1
  intro id row owner found use active
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  rw [frame.1] at inside
  have idOld : id < before.destinations.size := by
    by_cases old : id < before.destinations.size
    · exact old
    · have same : id = selected := by rw [fresh]; omega
      subst id
      have role := selectedRole row found
      rw [use] at role
      cases role
  have parentOld : owner < id := by
    by_cases eq : id = incoming
    · subst id
      have same := Option.some.inj (parent.symm.trans found)
      subst row
      have oldUse : receiver.use = .child owner := by simpa only using use
      simpa only [oldUse] using ordered incoming receiver present
    · have beforeFound : before.destinations[id]? = some row := by
        rw [← frame.2 id eq idOld]
        exact found
      simpa only [use] using ordered id row beforeFound
  have oldFound : ∃ oldRow, before.destinations[id]? = some oldRow ∧
      oldRow.use = .child owner ∧ activeRow oldRow = true := by
    by_cases eq : id = incoming
    · subst id
      have same := Option.some.inj (parent.symm.trans found)
      subst row
      refine ⟨receiver, present, ?_, ?_⟩
      · simpa only using use
      · simp [activeRow, opened]
    · refine ⟨row, ?_, use, active⟩
      rw [← frame.2 id eq idOld]
      exact found
  obtain ⟨oldRow, oldPresent, oldUse, oldActive⟩ := oldFound
  obtain ⟨oldOwner, ownerFound, blocked⟩ := valid id oldRow owner oldPresent oldUse oldActive
  by_cases ownerIsIncoming : owner = incoming
  · subst owner
    refine ⟨{ receiver with progress := .exiting count selected }, parent, ?_⟩
    exact Or.inr ⟨count, selected, rfl⟩
  · have ownerInside : owner < before.destinations.size := Nat.lt_trans parentOld idOld
    have afterFound : after.destinations[owner]? = some oldOwner := by
      rw [frame.2 owner ownerIsIncoming ownerInside]
      exact ownerFound
    exact ⟨oldOwner, afterFound, blocked⟩

theorem reserve_open_preserves_blocked_children (before after : ConstructionState)
    (incoming selected token count : Nat) (receiver : PendingDestination) (storage : ReceivingStorage)
    (present : before.destinations[incoming]? = some receiver) (opened : receiver.progress = .open (count + 1))
    (stored : before.storage[receiver.storage]? = some storage)
    (current : destinationCurrent before incoming = .ok incoming)
    (ordered : DestinationOwnersOrdered before) (valid : ActiveChildParentBlocked before)
    (reserved : reserveExitDestination incoming .newValue before = .ok (token, selected) after) :
    ActiveChildParentBlocked after := by
  have renewal : renewReceivingDestination incoming before = .ok incoming before := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, present, opened]
  have frontier : exitFrontierAction (before.destinations.size + 1) incoming before = .ok incoming before :=
    exitFrontier_open before.destinations.size incoming (count + 1) before receiver present opened
  rw [reserveExitDestination_equation] at reserved
  simp only [show (ExitSource.newValue == ExitSource.namedResult) = false from rfl,
    Bool.false_eq_true, ↓reduceIte, renewal, bind, ConstructionM.get, frontier,
    reserveLookupStep, lookupDestination_result, present, opened, Bool.false_or] at reserved
  cases replacement : openExitReplacement incoming before with
  | fault reason state => simp only [replacement] at reserved; cases reserved
  | ok picked state =>
    simp only [replacement, ConstructionM.get, ConstructionM.set, bind, pure, ConstructionResult.ok.injEq] at reserved
    obtain ⟨samePair, rfl⟩ := reserved
    cases samePair
    exact open_replacement_preserves_blocked_children before state incoming selected (count + 1) receiver storage
      present opened stored ordered valid replacement

#print axioms reserve_open_preserves_blocked_children
#print axioms open_replacement_preserves_blocked_children

end Goose.Proofs.ConstructionAcceptedExecution
