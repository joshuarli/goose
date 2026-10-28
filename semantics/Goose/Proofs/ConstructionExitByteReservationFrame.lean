import Goose.Proofs.ConstructionExitByteReservationStorage

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionRepresentation

theorem open_replacement_other_rows (before after : ConstructionState) (incoming selected count : Nat)
    (row : PendingDestination) (storage : ReceivingStorage)
    (present : before.destinations[incoming]? = some row) (opened : row.progress = .open count)
    (stored : before.storage[row.storage]? = some storage)
    (executed : openExitReplacement incoming before = .ok selected after) :
    after.destinations.size = before.destinations.size + 1 ∧
    ∀ other, other ≠ incoming → other < before.destinations.size →
      after.destinations[other]? = before.destinations[other]? := by
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
      simp only [Array.size_set!, Array.size_push, true_and] <;>
      intro other distinct bound <;>
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne,
        Ne.symm distinct, Array.getElem?_push, Nat.ne_of_lt bound]

theorem reserve_open_other_rows (before after : ConstructionState) (incoming selected token count : Nat)
    (row : PendingDestination) (storage : ReceivingStorage)
    (present : before.destinations[incoming]? = some row) (opened : row.progress = .open (count + 1))
    (stored : before.storage[row.storage]? = some storage)
    (current : destinationCurrent before incoming = .ok incoming)
    (reserved : reserveExitDestination incoming .newValue before = .ok (token, selected) after) :
    after.destinations.size = before.destinations.size + 1 ∧
    ∀ other, other ≠ incoming → other < before.destinations.size →
      after.destinations[other]? = before.destinations[other]? := by
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
    exact open_replacement_other_rows before state incoming selected (count + 1) row storage present opened stored replacement

theorem reserve_open_protected_named_rows (layout : LayoutEnv)
    (before after : ExecutionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (reserved : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) after.construction)
    (live : Goose.Core.RootInst → Prop) (region : ReceivingRegion)
    (destination : region.destination = incoming) (protection : ReceivingProtection layout before live region) :
    ∀ root, live root → ¬ region.mutableRoots root → ∀ value, before.objects.lookup root = some value →
      ∀ stored, StoredOccurrence value stored → ∀ id, stored.destination = some id →
      after.construction.destinations[id]? = before.construction.destinations[id]? := by
  have frame := reserve_open_other_rows before.construction after.construction incoming selected token count
    receiver.destination receiver.storage receiver.present receiver.opened receiver.bytes current reserved
  intro root active immutable value found stored occurrence id named
  have outside := protection.names root active immutable value found stored occurrence id named
  have distinct : id ≠ incoming := by
    intro equal
    subst id
    apply outside
    simpa only [destination] using protection.authority
  have backing := (protection.observations.backing.values root ⟨active, immutable⟩ value found).occurrence_backing
    layout before value stored occurrence
  cases backing with
  | detached storage element present detached type interval =>
    rw [detached] at named
    cases named
  | named old storage row count present selected binding rest =>
    have equal := Option.some.inj (selected.symm.trans named)
    subst old
    exact frame.2 id distinct (Array.getElem?_eq_some_iff.mp binding).1

#print axioms reserve_open_protected_named_rows
#print axioms open_replacement_other_rows
#print axioms reserve_open_other_rows

end Goose.Proofs.ConstructionAcceptedExecution
