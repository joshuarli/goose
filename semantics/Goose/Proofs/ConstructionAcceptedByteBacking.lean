import Goose.Proofs.ConstructionAcceptedOwnerLineage
import Goose.Proofs.ConstructionAcceptedElementWrite
import Goose.Proofs.ConstructionPackedSourceBacking

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionStorage
open Goose.Proofs.ConstructionExecutionProtocol

theorem byte_elementsEnd_exact (fuel : Nat) (layout : LayoutEnv) (bytes : ByteArray)
    (count start finish : Nat)
    (scanned : elementsEnd fuel layout (.int .u8) count bytes start = .ok finish) :
    finish = start + count := by
  induction fuel generalizing count start with
  | zero => simp only [elementsEnd, reduceCtorEq] at scanned
  | succ fuel ih =>
    cases count with
    | zero => simp only [elementsEnd, Except.ok.injEq] at scanned; omega
    | succ count =>
      cases fuel with
      | zero => simp only [elementsEnd, packedEnd, bind, Except.bind, reduceCtorEq] at scanned
      | succ fuel =>
        simp only [elementsEnd, packedEnd, fixedByteSize?] at scanned
        split at scanned
        · simp only [bind, Except.bind, reduceCtorEq] at scanned
        · simp only [pure, Except.pure, bind, Except.bind] at scanned
          have result := ih count (start + 1) scanned
          omega

theorem bytes_writeLoop_open_backing (bytes : List UInt8) (layout : LayoutEnv) (origin : Goose.Core.OriginId)
    (id count : Nat) (before after : ExecutionState)
    (ready : OpenDestinationBacking layout before id (.varr (.int .u8)) count)
    (current : destinationCurrent before.construction id = .ok id)
    (executed : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin id (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) before = .ok PUnit.unit after) :
    ∃ following : OpenDestinationBacking layout after id (.varr (.int .u8)) (count + bytes.length),
      following.destination.layout = ready.destination.layout ∧
      following.destination.capability = ready.destination.capability := by
  induction bytes generalizing before count with
  | nil =>
    simp only [List.forIn_nil, pure, ExecutionStep.ok.injEq, true_and] at executed
    subst after
    exact ⟨ready, rfl, rfl⟩
  | cons byte rest ih =>
    have renewal : renewReceivingDestination id before.construction = .ok id before.construction := by
      simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
        lookupDestination_result, ready.present, ready.opened]
    simp only [List.forIn_cons, receivingAction, liftConstruction, renewal, bind] at executed
    cases written : writeElement id ⟨#[byte]⟩ before.construction with
    | fault reason final => simp only [written] at executed; cases executed
    | ok value final =>
      cases value
      simp only [written, pure] at executed
      have element : ready.element = .int .u8 := by
        simpa only [elementType, Option.some.injEq] using ready.elementType.symm
      have encoded : ∃ fuel, packedEnd fuel layout ready.element ⟨#[byte]⟩ 0 = .ok (⟨#[byte]⟩ : ByteArray).size := by
        refine ⟨1, ?_⟩
        rw [element]
        rfl
      obtain ⟨next⟩ := writeElement_open_backing layout before final id (.varr (.int .u8)) count
        ⟨#[byte]⟩ ready encoded written
      have destination := writeElement_success_destination id ⟨#[byte]⟩ before.construction final
        ready.destination count ready.present ready.opened written
      have same : next.destination = { ready.destination with progress := .open (count + 1), writeEnd := ready.destination.writeEnd + (⟨#[byte]⟩ : ByteArray).size } :=
        Option.some.inj (next.present.symm.trans destination.1)
      have indexing := writeElement_preserves_indexing id ⟨#[byte]⟩ before.construction
      rw [written] at indexing
      simp only [ConstructionResult.finalState] at indexing
      have current' : destinationCurrent final id = .ok id := by
        rw [destinationCurrent_result, destinationCurrentSteps_same_indexing _ before.construction final indexing.1 indexing.2, indexing.1]
        simpa only [destinationCurrent_result] using current
      obtain ⟨following, layoutSame, capabilitySame⟩ :=
        ih (count + 1) { before with construction := final } next current' executed
      have length : count + (byte :: rest).length = (count + 1) + rest.length := by simp; omega
      rw [length]
      refine ⟨following, ?_, ?_⟩
      · simpa only [same] using layoutSame
      · simpa only [same] using capabilitySame

theorem finished_byteOwner_backing (layout : LayoutEnv) (before : ExecutionState) (after : ConstructionState)
    (id count : Nat) (ready : OpenDestinationBacking layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (fits : count < 2 ^ 32) (executed : finishDestination id before.construction = .ok () after) :
    ∃ value, storedDestination id { before with construction := after } =
      .ok value { before with construction := after } ∧
      Goose.Proofs.ConstructionRepresentation.StoredValueBacking layout { before with construction := after } value := by
  have element : ready.element = .int .u8 := by
    simpa only [elementType, Option.some.injEq] using ready.elementType.symm
  have scanned := ready.scan
  rw [element] at scanned
  have ending := byte_elementsEnd_exact ready.fuel layout ready.storage.bytes count
    (destinationPayloadStart ready.destination) ready.destination.writeEnd scanned
  have start : destinationPayloadStart ready.destination = ready.destination.capability.start + 4 := by
    simp only [destinationPayloadStart, packed, request, beq_self_eq_true, Bool.true_and, ↓reduceIte]
  have bounded : ready.destination.capability.start + 4 + count ≤ ready.storage.bytes.size := by
    rw [start] at ending
    have bound := ready.bounded
    omega
  obtain ⟨value, storage, present, sampled, backed, measured⟩ :=
    Goose.Proofs.ConstructionRepresentation.finishDestination_varrByte_backing layout before after id
      ready.destination ready.storage count ready.present ready.bytes ready.opened packed request
      ready.logicalType bounded fits executed
  exact ⟨value, sampled, backed⟩

theorem bytes_writeLoop_finished_backing (bytes : List UInt8) (layout : LayoutEnv) (origin : Goose.Core.OriginId)
    (id count : Nat) (before middle : ExecutionState) (after : ConstructionState)
    (ready : OpenDestinationBacking layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (fits : count + bytes.length < 2 ^ 32)
    (current : destinationCurrent before.construction id = .ok id)
    (loop : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin id (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) before = .ok PUnit.unit middle)
    (finished : finishDestination id middle.construction = .ok () after) :
    ∃ value, storedDestination id { middle with construction := after } =
      .ok value { middle with construction := after } ∧
      Goose.Proofs.ConstructionRepresentation.StoredValueBacking layout { middle with construction := after } value := by
  obtain ⟨following, sameLayout, sameCapability⟩ :=
    bytes_writeLoop_open_backing bytes layout origin id count before middle ready current loop
  apply finished_byteOwner_backing layout middle after id (count + bytes.length) following
  · exact sameLayout.trans packed
  · rw [sameCapability]; exact request
  · exact fits
  · exact finished

theorem buildExpr_byteOwner_backing (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (bytes : List UInt8) (origin : Goose.Core.OriginId) (id count : Nat) (before after : ExecutionState)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (fits : count + bytes.length < 2 ^ 32)
    (valid : DestinationLifecycleInvariant before.construction)
    (current : destinationCurrent before.construction id = .ok id)
    (executed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    ∃ value, storedDestination id after = .ok value after ∧
      Goose.Proofs.ConstructionRepresentation.StoredValueBacking config.layout after value := by
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
    obtain ⟨source, valid', current', row, n, present, opened⟩ :=
      bytes_writeLoop_ownershipSource bytes origin id before middle ready.destination count valid current
        ready.present ready.opened loop
    have renewal' : renewReceivingDestination id middle.construction = .ok id middle.construction := by
      simp only [renewReceivingDestination, ConstructionM.get, bind, current', pure,
        lookupDestination_result, present, opened]
    have loop' := loop
    simp only [bind] at loop'
    rw [loop'] at action
    simp only [receivingAction, liftConstruction, renewal', bind] at action
    cases finished : finishDestination id middle.construction with
    | fault reason final => simp only [finished] at action; cases action
    | ok value final =>
      cases value
      simp only [finished, ExecutionStep.ok.injEq, true_and] at action
      subst after
      exact bytes_writeLoop_finished_backing bytes config.layout origin id count before middle final
        ready packed request fits current loop finished

#print axioms bytes_writeLoop_open_backing
#print axioms byte_elementsEnd_exact
#print axioms finished_byteOwner_backing
#print axioms bytes_writeLoop_finished_backing
#print axioms buildExpr_byteOwner_backing

end Goose.Proofs.ConstructionAcceptedExecution
