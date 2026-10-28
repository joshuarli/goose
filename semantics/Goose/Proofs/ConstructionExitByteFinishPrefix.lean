import Goose.Proofs.ConstructionExitByteLoopPrefix
import Goose.Proofs.ExitExecutionCleanupStorageLanding
import Goose.Proofs.ConstructionExitByteCapability

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ExitExecution
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem finish_packed_byte_storage_prefix (layout : LayoutEnv) (before : ExecutionState)
    (after : ConstructionState) (id count : Nat) (limit : Nat → Nat)
    (ready : OpenDestinationBacking layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (cutoff : limit ready.destination.storage ≤ ready.destination.capability.start)
    (executed : finishDestination id before.construction = .ok () after) :
    StoragePrefixesEqual limit before.construction.storage after.storage := by
  have monotone := elementsEnd_monotone ready.fuel layout ready.element count ready.storage.bytes
    (destinationPayloadStart ready.destination) ready.destination.writeEnd ready.scan
  have bounded : limit ready.destination.storage ≤ ready.storage.bytes.size := by
    unfold destinationPayloadStart at monotone
    have bound := ready.bounded
    omega
  have inside := (Array.getElem?_eq_some_iff.mp ready.present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp ready.bytes).1
  simp only [finishDestination, writableDestination_result, ready.present, bind] at executed
  cases allowed : destinationCanWrite before.construction id with
  | false => simp only [allowed] at executed; cases executed
  | true =>
    simp only [allowed, ready.opened, packed, hasPrefix_result, request, beq_self_eq_true,
      Bool.and_self, ↓reduceIte, lookupStorage_result, ready.bytes, bind,
      replaceStorage_result, replaceDestination_result, storageInside, inside, pure] at executed
    cases executed
    have patch := sourcePatchCount_prefix ready.storage.bytes (limit ready.destination.storage)
      ready.destination.capability.start count bounded cutoff
    intro selected
    by_cases same : ready.destination.storage = selected
    · subst selected
      simp only [storagePrefixObservation, Array.set!, Array.getElem?_setIfInBounds_self_of_lt storageInside,
        ready.bytes, Option.map_some, patch]
    · simp only [storagePrefixObservation, Array.set!, Array.getElem?_setIfInBounds_ne same]

theorem build_packed_byte_storage_prefix (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (id count : Nat) (bytes : List UInt8)
    (origin : Goose.Core.OriginId) (before after : ExecutionState) (limit : Nat → Nat)
    (valid : OwnershipSourceState before.construction)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (cutoff : limit ready.destination.storage ≤ ready.destination.capability.start)
    (current : destinationCurrent before.construction id = .ok id)
    (executed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    StoragePrefixesEqual limit before.construction.storage after.construction.storage := by
  have renewal : renewReceivingDestination id before.construction = .ok id before.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, ready.present, ready.opened]
  simp only [buildExpr, liftConstruction, renewal, bind] at executed
  have action := protectDestination_success origin id _ before after () executed
  cases loop : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin id (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) before with
  | stop reason state => simp only [bind] at loop; rw [loop] at action; cases action
  | escape target carriers state => simp only [bind] at loop; rw [loop] at action; cases action
  | jump target kind state => simp only [bind] at loop; rw [loop] at action; cases action
  | ok value middle =>
    cases value
    have first := byte_writeLoop_storage_prefix bytes config.layout origin id count before middle limit ready cutoff current loop
    obtain ⟨following, sameLayout, sameCapability, sameBacking, sameUse⟩ :=
      bytes_writeLoop_open_backing bytes config.layout origin id count before middle ready current loop
    have sameStorage : following.destination.storage = ready.destination.storage := by
      simp only [PendingDestination.storage, sameBacking]
    have cutoff' : limit following.destination.storage ≤ following.destination.capability.start := by
      rw [sameStorage, sameCapability]
      exact cutoff
    obtain ⟨source, lifecycle, current', next, n, present', opened'⟩ :=
      bytes_writeLoop_ownershipSource bytes origin id before middle ready.destination count valid.structural.1.1.1 current ready.present ready.opened loop
    have renewal' : renewReceivingDestination id middle.construction = .ok id middle.construction := by
      simp only [renewReceivingDestination, ConstructionM.get, bind, current', pure,
        lookupDestination_result, present', opened']
    simp only [bind] at loop
    rw [loop] at action
    simp only [receivingAction, liftConstruction, renewal', bind] at action
    cases finished : finishDestination id middle.construction with
    | fault reason final => simp only [finished] at action; cases action
    | ok value final =>
      cases value
      simp only [finished, ExecutionStep.ok.injEq, true_and] at action
      subst after
      have last := finish_packed_byte_storage_prefix config.layout middle final id (count + bytes.length) limit following
        (sameLayout.trans packed) (by rw [sameCapability]; exact request) cutoff' finished
      intro selected
      exact (last selected).trans (first selected)

#print axioms finish_packed_byte_storage_prefix
#print axioms build_packed_byte_storage_prefix

end Goose.Proofs.ConstructionAcceptedExecution
