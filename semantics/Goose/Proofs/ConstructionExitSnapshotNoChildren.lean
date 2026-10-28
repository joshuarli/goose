import Goose.Proofs.ConstructionExitUnblockedRestore
import Goose.Proofs.ConstructionExitByteReservationFrame
import Goose.Proofs.ConstructionAcceptedOwnerLineage

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem open_destination_no_active_children (state : ConstructionState)
    (parent count : Nat) (receiver : PendingDestination)
    (present : state.destinations[parent]? = some receiver) (opened : receiver.progress = .open count)
    (blocked : ActiveChildParentBlocked state) : NoActiveChildren state parent := by
  intro id row found use active
  have inactive := activeChildParentBlocked_open_excludes_direct_child state blocked parent id count receiver row present opened found use
  rw [active] at inactive
  cases inactive

theorem reserve_open_replacement_use (before after : ConstructionState) (incoming selected token count : Nat)
    (row : PendingDestination) (present : before.destinations[incoming]? = some row)
    (opened : row.progress = .open (count + 1)) (current : destinationCurrent before incoming = .ok incoming)
    (reserved : reserveExitDestination incoming .newValue before = .ok (token, selected) after) :
    ∃ replacement, after.destinations[selected]? = some replacement ∧ replacement.use = .replacement incoming := by
  have renewal : renewReceivingDestination incoming before = .ok incoming before := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, present, opened]
  have frontier : exitFrontierAction (before.destinations.size + 1) incoming before = .ok incoming before :=
    exitFrontier_open before.destinations.size incoming (count + 1) before row present opened
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
    obtain ⟨parent, replacementRow, n, parentFound, phase, active, selectedFound, selectedUse⟩ :=
      openExitReplacement_new_parent_active before state incoming selected replacement
    exact ⟨replacementRow, selectedFound, selectedUse⟩

theorem reserve_open_preserves_no_children (before after : ConstructionState)
    (incoming selected token count : Nat) (receiver : PendingDestination) (storage : ReceivingStorage)
    (present : before.destinations[incoming]? = some receiver) (opened : receiver.progress = .open (count + 1))
    (stored : before.storage[receiver.storage]? = some storage) (current : destinationCurrent before incoming = .ok incoming)
    (ordered : DestinationOwnersOrdered before) (blocked : ActiveChildParentBlocked before)
    (reservation : reserveExitDestination incoming .newValue before = .ok (token, selected) after) :
    NoActiveChildren after incoming := by
  have noBefore := open_destination_no_active_children before incoming (count + 1) receiver present opened blocked
  have fresh := reserve_open_replacement_fresh before after incoming selected token count receiver storage present opened stored current reservation
  have frame := reserve_open_other_rows before after incoming selected token count receiver storage present opened stored current reservation
  have parent := (reserve_open_receiver_snapshot before after incoming selected token count receiver present opened current reservation).1
  obtain ⟨replacement, selectedFound, selectedUse⟩ := reserve_open_replacement_use before after incoming selected token count receiver present opened current reservation
  intro id row found use active
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  rw [frame.1] at inside
  by_cases isSelected : id = selected
  · subst id
    have same := Option.some.inj (selectedFound.symm.trans found)
    subst row
    rw [selectedUse] at use
    cases use
  · have old : id < before.destinations.size := by
      rw [fresh] at isSelected
      exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp inside) isSelected
    by_cases isParent : id = incoming
    · subst id
      have same := Option.some.inj (parent.symm.trans found)
      subst row
      have beforeUse : receiver.use = .child incoming := by simpa only using use
      have impossible : incoming < incoming := by simpa only [beforeUse] using ordered incoming receiver present
      exact Nat.lt_irrefl _ impossible
    · have original : before.destinations[id]? = some row := by
        rw [← frame.2 id isParent old]
        exact found
      exact noBefore id row original use active

theorem build_packed_bytes_preserves_no_children (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (selected count parent : Nat) (bytes : List UInt8) (origin : OriginId) (before after : ExecutionState)
    (valid : OwnershipSourceState before.construction)
    (ready : OpenDestinationBacking config.layout before selected (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction selected = .ok selected)
    (notChild : ready.destination.use ≠ .child parent) (noChildren : NoActiveChildren before.construction parent)
    (built : buildExpr (fuel + 1) config environment selected (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    NoActiveChildren after.construction parent := by
  have source := (buildExpr_bytes_ownershipSource fuel config environment selected (.varr (.int .u8)) bytes origin
    before after ready.destination count valid.structural.1.1.1 current ready.present ready.opened built).1
  obtain ⟨selectedRow, selectedFound, sameUse, backing⟩ := source selected ready.destination ready.present
  intro id row found use active
  by_cases same : id = selected
  · subst id
    have equal := Option.some.inj (selectedFound.symm.trans found)
    subst row
    exact notChild (sameUse.symm.trans use)
  · have frame := build_packed_bytes_other_row fuel config environment selected count id bytes origin before after
      valid ready packed request current same built
    exact noChildren id row (by rw [← frame]; exact found) use active

theorem reserved_byte_build_preserves_snapshot_no_children (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (receiverState before after : ExecutionState) (reserved : ConstructionState)
    (incoming selected token count writeCount : Nat) (bytes : List UInt8) (origin : OriginId)
    (receiver : OpenDestinationBacking config.layout receiverState incoming (.varr (.int .u8)) (count + 1))
    (receiverCurrent : destinationCurrent receiverState.construction incoming = .ok incoming)
    (ordered : DestinationOwnersOrdered receiverState.construction) (blocked : ActiveChildParentBlocked receiverState.construction)
    (reservation : reserveExitDestination incoming .newValue receiverState.construction = .ok (token, selected) reserved)
    (construction : before.construction = reserved) (valid : OwnershipSourceState before.construction)
    (ready : OpenDestinationBacking config.layout before selected (.varr (.int .u8)) writeCount)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction selected = .ok selected)
    (built : buildExpr (fuel + 1) config environment selected (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    NoActiveChildren after.construction incoming := by
  have noReserved := reserve_open_preserves_no_children receiverState.construction reserved incoming selected token count
    receiver.destination receiver.storage receiver.present receiver.opened receiver.bytes receiverCurrent ordered blocked reservation
  obtain ⟨replacement, found, use⟩ := reserve_open_replacement_use receiverState.construction reserved incoming selected token count
    receiver.destination receiver.present receiver.opened receiverCurrent reservation
  have same : replacement = ready.destination := Option.some.inj (found.symm.trans (by simpa only [construction] using ready.present))
  have notChild : ready.destination.use ≠ .child incoming := by
    rw [← same, use]
    intro impossible
    cases impossible
  apply build_packed_bytes_preserves_no_children fuel config environment selected writeCount incoming bytes origin before after
    valid ready packed request current notChild _ built
  simpa only [construction] using noReserved

#print axioms build_packed_bytes_preserves_no_children
#print axioms reserved_byte_build_preserves_snapshot_no_children
#print axioms open_destination_no_active_children
#print axioms reserve_open_replacement_use
#print axioms reserve_open_preserves_no_children

end Goose.Proofs.ConstructionAcceptedExecution
