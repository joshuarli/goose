import Goose.Proofs.ConstructionExitTargetProtectedRoots
import Goose.Proofs.ConstructionExitByteCapability
import Goose.Proofs.ConstructionExitByteProtectedBuild
import Goose.Proofs.ConstructionAcceptedBytePublication

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionStorage
open Goose.Proofs.ExitExecution

theorem bytes_writeLoop_rollback (bytes : List UInt8) (origin : OriginId) (id : Nat)
    (before after : ExecutionState) (row : PendingDestination) (count : Nat)
    (valid : OwnershipSourceState before.construction)
    (current : destinationCurrent before.construction id = .ok id)
    (present : before.construction.destinations[id]? = some row) (opened : row.progress = .open count)
    (executed : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin id (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) before = .ok PUnit.unit after) :
    ∃ result, after.construction.destinations[id]? = some result ∧
      result.rollbackEnd = row.rollbackEnd ∧ result.progress = .open (count + bytes.length) := by
  induction bytes generalizing before row count with
  | nil =>
    simp only [List.forIn_nil, pure, ExecutionStep.ok.injEq, true_and] at executed
    subst after
    exact ⟨row, present, rfl, by simpa using opened⟩
  | cons byte rest ih =>
    have renewal : renewReceivingDestination id before.construction = .ok id before.construction := by
      simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
        lookupDestination_result, present, opened]
    simp only [List.forIn_cons, receivingAction, liftConstruction, renewal, bind] at executed
    cases written : writeElement id ⟨#[byte]⟩ before.construction with
    | fault reason final => simp only [written] at executed; cases executed
    | ok value final =>
      cases value
      simp only [written, pure] at executed
      have extension := writeElement_ownership_source id ⟨#[byte]⟩ before.construction valid.structural.1.1.1
      have nextValid := constructionPrimitive_sourceState_of_sourceExtension (writeElement id ⟨#[byte]⟩)
        (.writeElement id ⟨#[byte]⟩) before.construction valid extension
      rw [written] at nextValid
      have nextRow := writeElement_success_destination id ⟨#[byte]⟩ before.construction final row count present opened written
      have indexing := writeElement_preserves_indexing id ⟨#[byte]⟩ before.construction
      rw [written] at indexing
      simp only [ConstructionResult.finalState] at indexing
      have nextCurrent : destinationCurrent final id = .ok id := by
        rw [destinationCurrent_result, destinationCurrentSteps_same_indexing _ before.construction final indexing.1 indexing.2, indexing.1]
        simpa only [destinationCurrent_result] using current
      obtain ⟨result, found, rollback, phase⟩ := ih { before with construction := final }
        { row with progress := .open (count + 1), writeEnd := row.writeEnd + (⟨#[byte]⟩ : ByteArray).size } (count + 1)
        nextValid nextCurrent nextRow.1 rfl executed
      refine ⟨result, found, rollback, ?_⟩
      have lengthEq : count + 1 + rest.length = count + (byte :: rest).length := by simp; omega
      simpa only [lengthEq] using phase

theorem build_packed_bytes_rollback (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (id count : Nat) (bytes : List UInt8) (origin : OriginId) (before after : ExecutionState)
    (valid : OwnershipSourceState before.construction)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id)
    (executed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    ∃ result, after.construction.destinations[id]? = some result ∧
      result.rollbackEnd = ready.destination.rollbackEnd ∧ result.progress = .built (count + bytes.length) := by
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
    obtain ⟨source, lifecycle, current', next, n, present', opened'⟩ :=
      bytes_writeLoop_ownershipSource bytes origin id before middle ready.destination count valid.structural.1.1.1 current ready.present ready.opened loop
    obtain ⟨following, found, rollback, phase⟩ := bytes_writeLoop_rollback bytes origin id before middle ready.destination count
      valid current ready.present ready.opened loop
    obtain ⟨backed, sameLayout, sameCapability, _, _⟩ := bytes_writeLoop_open_backing bytes config.layout origin id count before middle ready current loop
    have same : next = following := Option.some.inj (present'.symm.trans found)
    have sameBacked : next = backed.destination := Option.some.inj (present'.symm.trans backed.present)
    have countEq : n = count + bytes.length := by
      have phases : next.progress = .open (count + bytes.length) := by rw [same]; exact phase
      rw [opened'] at phases
      exact DestinationProgress.open.inj phases
    have packed' : next.layout = .packed := by rw [sameBacked, sameLayout, packed]
    have request' : next.capability.request = .value := by rw [sameBacked, sameCapability, request]
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
      refine ⟨{ next with progress := .built n }, finish_packed_byte_row middle.construction final id n next present' opened' packed' request' finished, ?_, ?_⟩
      · simpa only [same] using rollback
      · exact congrArg DestinationProgress.built countEq

theorem packed_byte_build_receiver_protection (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (id count : Nat) (bytes : List UInt8)
    (origin : OriginId) (before after : ExecutionState)
    (liveRoots : RootInst → Prop) (region : ReceivingRegion)
    (valid : OwnershipSourceState before.construction)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (fits : count + bytes.length < 2 ^ 32)
    (current : destinationCurrent before.construction id = .ok id)
    (selected : region.destination = id)
    (protection : ReceivingProtection config.layout before liveRoots region)
    (built : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    ReceivingProtection config.layout after liveRoots region := by
  obtain ⟨result, found, rollback, _⟩ := build_packed_bytes_rollback fuel config environment id count bytes origin before after valid ready packed request current built
  obtain ⟨capRow, capFound, capability, _⟩ := build_packed_bytes_capability fuel config environment id count bytes origin before after valid ready packed request current built
  obtain ⟨geomRow, storage, geomFound, _, _, _, _, backing, _, _, _⟩ := buildExpr_byteOwner_geometry fuel config environment bytes origin id count before after ready packed request fits valid.structural.1.1.1 current built
  have capSame : capRow = result := Option.some.inj (capFound.symm.trans found)
  have geomSame : geomRow = result := Option.some.inj (geomFound.symm.trans found)
  have capEq : result.capability = ready.destination.capability := by simpa only [capSame] using capability
  have storageEq : result.storage = ready.destination.storage := by
    simpa only [PendingDestination.storage, geomSame] using congrArg DestinationBacking.writeStorage backing
  have oldFound : before.construction.destinations[region.destination]? = some ready.destination := by simpa only [selected] using ready.present
  have cutoff := protection.landing ready.destination oldFound
  have prefixes := build_packed_byte_storage_prefix fuel config environment id count bytes origin before after region.limit valid ready packed request cutoff current built
  have runtime := buildExpr_bytes_runtime fuel config environment id _ bytes origin before after ready.destination count valid current ready.present ready.opened built
  have objects := congrArg ExecutionState.objects runtime
  have ordinals := congrArg ExecutionState.objectOrdinals runtime
  have size := (build_packed_bytes_indexing fuel config environment id count bytes origin before after valid ready packed request current built).1
  have mutable : id ∈ region.mutableDestinations := by simpa only [selected] using protection.authority
  refine ⟨⟨result, by simpa only [selected] using found⟩, ?_, ?_, ?_, protection.authority, ?_, ?_⟩
  · apply rootedBackingObservations_storagePrefixes config.layout before after _ region.limit protection.observations prefixes objects ordinals
    intro root kept value present stored occurrence other destination
    have nonmember := protection.names root kept.1 kept.2 value present stored occurrence other destination
    have distinct : other ≠ id := by intro equal; subst other; exact nonmember mutable
    exact build_packed_bytes_other_row fuel config environment id count other bytes origin before after valid ready packed request current distinct built
  · intro row rowFound
    have rowFound' : after.construction.destinations[id]? = some row := by simpa only [selected] using rowFound
    have same : row = result := Option.some.inj (rowFound'.symm.trans found)
    rw [same, storageEq, rollback]
    exact protection.cutoff ready.destination oldFound
  · intro row rowFound
    have rowFound' : after.construction.destinations[id]? = some row := by simpa only [selected] using rowFound
    have same : row = result := Option.some.inj (rowFound'.symm.trans found)
    rw [same, storageEq, capEq]
    exact cutoff
  · intro other member
    rw [size]
    exact protection.authorityBound other member
  · intro root live immutable value present stored occurrence other destination
    apply protection.names root live immutable value _ stored occurrence other destination
    simpa only [objects] using present

#print axioms packed_byte_build_receiver_protection

#print axioms bytes_writeLoop_rollback
#print axioms build_packed_bytes_rollback

end Goose.Proofs.ConstructionAcceptedExecution
