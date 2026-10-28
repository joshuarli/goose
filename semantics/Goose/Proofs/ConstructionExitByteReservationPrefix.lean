import Goose.Proofs.ConstructionExitByteReservationFrame

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem open_replacement_storage_prefix (before after : ConstructionState) (incoming selected count : Nat)
    (row : PendingDestination) (storage : ReceivingStorage) (limit : Nat → Nat)
    (present : before.destinations[incoming]? = some row) (opened : row.progress = .open count)
    (stored : before.storage[row.storage]? = some storage)
    (bounded : limit row.storage ≤ storage.bytes.size)
    (executed : openExitReplacement incoming before = .ok selected after) :
    StoragePrefixesEqual limit before.storage after.storage := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  simp only [openExitReplacement, writableDestination_result, present, bind] at executed
  cases allowed : destinationCanWrite before incoming with
  | false => simp [allowed] at executed
  | true =>
    simp only [allowed, opened, pure, bind, lookupStorage_result, stored, ConstructionM.get,
      ConstructionM.set, replaceDestination_result, replaceStorage_result, emit_result,
      Array.size_push, Nat.lt_succ_of_lt inside, storageInside, Array.size_setIfInBounds, ↓reduceIte] at executed
    split at executed
    · simp only [Nat.lt_succ_of_lt inside, storageInside, ↓reduceIte, bind, pure] at executed
      cases executed
      have prefixEq (suffix : ByteArray) : (storage.bytes ++ suffix).extract 0 (limit row.storage) =
          storage.bytes.extract 0 (limit row.storage) := by
        have full : (storage.bytes ++ suffix).extract 0 storage.bytes.size = storage.bytes :=
          ByteArray.extract_append_eq_left rfl
        have restricted := congrArg (fun bytes : ByteArray => bytes.extract 0 (limit row.storage)) full
        simpa only [ByteArray.extract_extract, Nat.zero_add, Nat.min_eq_left bounded] using restricted
      intro other
      by_cases same : row.storage = other
      · subst other
        simp only [storagePrefixObservation, Array.set!, Array.getElem?_setIfInBounds_self_of_lt storageInside,
          stored, Option.map_some, prefixEq]
      · simp only [storagePrefixObservation, Array.set!, Array.getElem?_setIfInBounds_ne same]
    · simp only [Nat.lt_succ_of_lt inside, storageInside, ↓reduceIte, bind, pure] at executed
      cases executed
      intro other
      rfl

theorem reserve_open_storage_prefix (before after : ConstructionState) (incoming selected token count : Nat)
    (row : PendingDestination) (storage : ReceivingStorage) (limit : Nat → Nat)
    (present : before.destinations[incoming]? = some row) (opened : row.progress = .open (count + 1))
    (stored : before.storage[row.storage]? = some storage) (bounded : limit row.storage ≤ storage.bytes.size)
    (current : destinationCurrent before incoming = .ok incoming)
    (reserved : reserveExitDestination incoming .newValue before = .ok (token, selected) after) :
    StoragePrefixesEqual limit before.storage after.storage := by
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
    exact open_replacement_storage_prefix before state incoming selected (count + 1) row storage limit
      present opened stored bounded replacement

theorem reserve_open_extended_protection (layout : LayoutEnv) (before : ExecutionState)
    (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (live : Goose.Core.RootInst → Prop) (region : ReceivingRegion)
    (destination : region.destination = incoming) (protection : ReceivingProtection layout before live region) :
    ReceivingProtection layout { before with construction := reserved } live
      { region with mutableDestinations := selected :: region.mutableDestinations } := by
  let after : ExecutionState := { before with construction := reserved }
  have parent := (reserve_open_receiver_snapshot before.construction reserved incoming selected token count
    receiver.destination receiver.present receiver.opened current reservation).1
  have frame := reserve_open_other_rows before.construction reserved incoming selected token count
    receiver.destination receiver.storage receiver.present receiver.opened receiver.bytes current reservation
  have fresh := reserve_open_replacement_fresh before.construction reserved incoming selected token count
    receiver.destination receiver.storage receiver.present receiver.opened receiver.bytes current reservation
  have landing := protection.landing receiver.destination (by simpa only [destination] using receiver.present)
  have monotone := elementsEnd_monotone receiver.fuel layout receiver.element (count + 1) receiver.storage.bytes
    (destinationPayloadStart receiver.destination) receiver.destination.writeEnd receiver.scan
  have cutoffStorage : region.limit receiver.destination.storage ≤ receiver.storage.bytes.size := by
    have bound := receiver.bounded
    unfold destinationPayloadStart at monotone
    omega
  have prefixes := reserve_open_storage_prefix before.construction reserved incoming selected token count
    receiver.destination receiver.storage region.limit receiver.present receiver.opened receiver.bytes cutoffStorage current reservation
  have rows := reserve_open_protected_named_rows layout before after incoming selected token count receiver current
    reservation live region destination protection
  have noFresh := reserved_byte_excludes_protected_names layout before.construction reserved incoming selected token count
    before rfl receiver current reservation live region protection
  have observations := rootedBackingObservations_storagePrefixes layout before after _ region.limit protection.observations prefixes rfl rfl
    (by intro root kept value found stored occurrence id named; exact rows root kept.1 kept.2 value found stored occurrence id named)
  refine ⟨?_, observations, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨{ receiver.destination with progress := .exiting (count + 1) selected }, by simpa only [destination] using parent⟩
  · intro row found
    have same : row = { receiver.destination with progress := .exiting (count + 1) selected } :=
      Option.some.inj (found.symm.trans (by simpa only [destination] using parent))
    rw [same]
    exact protection.cutoff receiver.destination (by simpa only [destination] using receiver.present)
  · intro row found
    have same : row = { receiver.destination with progress := .exiting (count + 1) selected } :=
      Option.some.inj (found.symm.trans (by simpa only [destination] using parent))
    rw [same]
    exact landing
  · simp only [List.mem_cons]
    exact Or.inr protection.authority
  · intro id member
    simp only [List.mem_cons] at member
    rw [frame.1]
    rcases member with rfl | old
    · rw [fresh]
      omega
    · have bounded := protection.authorityBound id old
      omega
  · intro root active immutable value found stored occurrence id named
    simp only [List.mem_cons, not_or]
    refine ⟨?_, protection.names root active immutable value found stored occurrence id named⟩
    intro equal
    subst id
    exact noFresh root active immutable value found stored occurrence named

theorem reserved_packed_byte_build_protection (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (before : ExecutionState) (reserved : ConstructionState)
    (after : ExecutionState) (incoming selected token count writeCount : Nat) (bytes : List UInt8)
    (origin : Goose.Core.OriginId)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (receiverCurrent : destinationCurrent before.construction incoming = .ok incoming)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (valid : OwnershipSourceState reserved)
    (ready : OpenDestinationBacking config.layout { before with construction := reserved } selected (.varr (.int .u8)) writeCount)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent reserved selected = .ok selected)
    (live : Goose.Core.RootInst → Prop) (region : ReceivingRegion)
    (destination : region.destination = incoming) (protection : ReceivingProtection config.layout before live region)
    (built : buildExpr (fuel + 1) config environment selected (.bytes (.varr (.int .u8)) bytes origin)
      { before with construction := reserved } = .ok () after) :
    ReceivingProtection config.layout after live
      { region with mutableDestinations := selected :: region.mutableDestinations } := by
  have extended := reserve_open_extended_protection config.layout before reserved incoming selected token count
    receiver receiverCurrent reservation live region destination protection
  have cutoff := reserved_byte_protection_cutoff config.layout before.construction reserved incoming selected token count writeCount
    before { before with construction := reserved } rfl receiver receiverCurrent reservation rfl ready live region destination protection
  have fresh := reserve_open_replacement_fresh before.construction reserved incoming selected token count
    receiver.destination receiver.storage receiver.present receiver.opened receiver.bytes receiverCurrent reservation
  have bound := (Array.getElem?_eq_some_iff.mp receiver.present).1
  have different : region.destination ≠ selected := by rw [destination, fresh]; omega
  exact packed_byte_build_protection fuel config environment selected writeCount bytes origin
    { before with construction := reserved } after live
    { region with mutableDestinations := selected :: region.mutableDestinations }
    valid ready packed request current different (by simp) cutoff extended built

#print axioms reserved_packed_byte_build_protection
#print axioms reserve_open_extended_protection
#print axioms open_replacement_storage_prefix
#print axioms reserve_open_storage_prefix

end Goose.Proofs.ConstructionAcceptedExecution
