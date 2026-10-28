import Goose.Proofs.ConstructionExitReplacementOffset
import Goose.Proofs.ConstructionExitByteProtectedBuild

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ExitExecution

theorem open_replacement_storage (before after : ConstructionState) (incoming selected count : Nat)
    (row : PendingDestination) (storage : ReceivingStorage)
    (present : before.destinations[incoming]? = some row) (opened : row.progress = .open count)
    (stored : before.storage[row.storage]? = some storage)
    (executed : openExitReplacement incoming before = .ok selected after) :
    ∃ replacement, after.destinations[selected]? = some replacement ∧ replacement.storage = row.storage := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  simp only [openExitReplacement, writableDestination_result, present, bind] at executed
  cases allowed : destinationCanWrite before incoming with
  | false => simp [allowed] at executed
  | true =>
    simp only [allowed, opened, pure, bind, lookupStorage_result, stored, ConstructionM.get,
      ConstructionM.set, replaceDestination_result, replaceStorage_result, emit_result,
      Array.size_push, Nat.lt_succ_of_lt inside, storageInside, Array.size_setIfInBounds, ↓reduceIte] at executed
    split at executed <;>
      simp only [Nat.lt_succ_of_lt inside, storageInside, ↓reduceIte, bind, pure] at executed <;>
      cases executed <;>
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne,
        Nat.ne_of_lt inside, Array.getElem?_push, PendingDestination.storage]

theorem open_replacement_fresh (before after : ConstructionState) (incoming selected count : Nat)
    (row : PendingDestination) (storage : ReceivingStorage)
    (present : before.destinations[incoming]? = some row) (opened : row.progress = .open count)
    (stored : before.storage[row.storage]? = some storage)
    (executed : openExitReplacement incoming before = .ok selected after) :
    selected = before.destinations.size := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  simp only [openExitReplacement, writableDestination_result, present, bind] at executed
  cases allowed : destinationCanWrite before incoming with
  | false => simp [allowed] at executed
  | true =>
    simp only [allowed, opened, pure, bind, lookupStorage_result, stored, ConstructionM.get,
      ConstructionM.set, replaceDestination_result, replaceStorage_result, emit_result,
      Array.size_push, Nat.lt_succ_of_lt inside, storageInside, Array.size_setIfInBounds, ↓reduceIte] at executed
    split at executed <;>
      simp only [Nat.lt_succ_of_lt inside, storageInside, ↓reduceIte, bind, pure] at executed <;>
      cases executed <;>
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne,
        Nat.ne_of_lt inside, Array.getElem?_push, PendingDestination.storage]

theorem reserve_open_replacement_storage (before after : ConstructionState) (incoming selected token count : Nat)
    (row : PendingDestination) (storage : ReceivingStorage)
    (present : before.destinations[incoming]? = some row) (opened : row.progress = .open (count + 1))
    (stored : before.storage[row.storage]? = some storage)
    (current : destinationCurrent before incoming = .ok incoming)
    (reserved : reserveExitDestination incoming .newValue before = .ok (token, selected) after) :
    ∃ replacement, after.destinations[selected]? = some replacement ∧ replacement.storage = row.storage := by
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
    exact open_replacement_storage before state incoming selected (count + 1) row storage present opened stored replacement

theorem reserve_open_replacement_fresh (before after : ConstructionState) (incoming selected token count : Nat)
    (row : PendingDestination) (storage : ReceivingStorage)
    (present : before.destinations[incoming]? = some row) (opened : row.progress = .open (count + 1))
    (stored : before.storage[row.storage]? = some storage)
    (current : destinationCurrent before incoming = .ok incoming)
    (reserved : reserveExitDestination incoming .newValue before = .ok (token, selected) after) :
    selected = before.destinations.size := by
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
    exact open_replacement_fresh before state incoming selected (count + 1) row storage present opened stored replacement

theorem reserved_byte_protection_cutoff (layout : LayoutEnv)
    (reservationBefore reserved : ConstructionState) (incoming selected token count writeCount : Nat)
    (receiverState before : ExecutionState) (receiverConstruction : receiverState.construction = reservationBefore)
    (receiver : OpenDestinationBacking layout receiverState incoming (.varr (.int .u8)) (count + 1))
    (receiverCurrent : destinationCurrent reservationBefore incoming = .ok incoming)
    (reservation : reserveExitDestination incoming .newValue reservationBefore = .ok (token, selected) reserved)
    (construction : before.construction = reserved)
    (ready : OpenDestinationBacking layout before selected (.varr (.int .u8)) writeCount)
    (live : Goose.Core.RootInst → Prop) (region : ReceivingRegion) (destination : region.destination = incoming)
    (protection : ReceivingProtection layout receiverState live region) :
    region.limit ready.destination.storage ≤ ready.destination.capability.start := by
  have present : reservationBefore.destinations[incoming]? = some receiver.destination := by
    simpa only [receiverConstruction] using receiver.present
  have stored : reservationBefore.storage[receiver.destination.storage]? = some receiver.storage := by
    simpa only [receiverConstruction] using receiver.bytes
  obtain ⟨replacement, found, sameStorage⟩ := reserve_open_replacement_storage reservationBefore reserved
    incoming selected token count receiver.destination receiver.storage present receiver.opened stored receiverCurrent reservation
  obtain ⟨replacement', found', start⟩ := reserve_open_replacement_start reservationBefore reserved
    incoming selected token count receiver.destination receiver.storage present receiver.opened stored receiverCurrent reservation
  have same : replacement = ready.destination := Option.some.inj (found.symm.trans (by simpa only [construction] using ready.present))
  have same' : replacement' = ready.destination := Option.some.inj (found'.symm.trans (by simpa only [construction] using ready.present))
  have landing := protection.landing receiver.destination (by simpa only [destination] using receiver.present)
  have monotone := elementsEnd_monotone receiver.fuel layout receiver.element (count + 1) receiver.storage.bytes
    (destinationPayloadStart receiver.destination) receiver.destination.writeEnd receiver.scan
  have bounded := receiver.bounded
  rw [same] at sameStorage
  rw [same'] at start
  rw [sameStorage, start]
  unfold destinationPayloadStart at monotone
  omega

theorem rooted_backing_excludes_fresh_destination (layout : LayoutEnv) (state : ExecutionState)
    (retained : Goose.Core.RootInst → Prop) (limit : Nat → Nat)
    (valid : RootedBackingObservations layout state retained limit) (fresh : Nat)
    (frontier : state.construction.destinations.size ≤ fresh) :
    ∀ root, retained root → ∀ value, state.objects.lookup root = some value →
      ∀ stored, StoredOccurrence value stored → stored.destination ≠ some fresh := by
  intro root kept value found stored occurrence named
  have backing := (valid.backing.values root kept value found).occurrence_backing layout state value stored occurrence
  cases backing with
  | detached storage element present detached type interval =>
    rw [detached] at named
    cases named
  | named id storage destination count present selected binding rest =>
    have equal : id = fresh := Option.some.inj (selected.symm.trans named)
    subst id
    have bound := (Array.getElem?_eq_some_iff.mp binding).1
    omega

theorem reserved_byte_excludes_protected_names (layout : LayoutEnv)
    (reservationBefore reserved : ConstructionState) (incoming selected token count : Nat)
    (receiverState : ExecutionState) (receiverConstruction : receiverState.construction = reservationBefore)
    (receiver : OpenDestinationBacking layout receiverState incoming (.varr (.int .u8)) (count + 1))
    (receiverCurrent : destinationCurrent reservationBefore incoming = .ok incoming)
    (reservation : reserveExitDestination incoming .newValue reservationBefore = .ok (token, selected) reserved)
    (live : Goose.Core.RootInst → Prop) (region : ReceivingRegion)
    (protection : ReceivingProtection layout receiverState live region) :
    ∀ root, live root → ¬ region.mutableRoots root → ∀ value, receiverState.objects.lookup root = some value →
      ∀ stored, StoredOccurrence value stored → stored.destination ≠ some selected := by
  have present : reservationBefore.destinations[incoming]? = some receiver.destination := by
    simpa only [receiverConstruction] using receiver.present
  have stored : reservationBefore.storage[receiver.destination.storage]? = some receiver.storage := by
    simpa only [receiverConstruction] using receiver.bytes
  have fresh := reserve_open_replacement_fresh reservationBefore reserved incoming selected token count
    receiver.destination receiver.storage present receiver.opened stored receiverCurrent reservation
  have frontier : receiverState.construction.destinations.size ≤ selected := by
    rw [receiverConstruction, fresh]
    exact Nat.le_refl _
  intro root active immutable
  exact rooted_backing_excludes_fresh_destination layout receiverState _ region.limit protection.observations selected frontier root ⟨active, immutable⟩

#print axioms reserved_byte_excludes_protected_names
#print axioms open_replacement_fresh
#print axioms reserve_open_replacement_fresh
#print axioms rooted_backing_excludes_fresh_destination
#print axioms reserved_byte_protection_cutoff
#print axioms open_replacement_storage
#print axioms reserve_open_replacement_storage

end Goose.Proofs.ConstructionAcceptedExecution
