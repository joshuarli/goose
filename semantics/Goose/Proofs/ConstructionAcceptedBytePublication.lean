import Goose.Proofs.ConstructionAcceptedByteAllocation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionProtocol

theorem finished_byteOwner_geometry (layout : LayoutEnv) (before : ExecutionState) (after : ConstructionState)
    (id count : Nat) (ready : OpenDestinationBacking layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (fits : count < 2 ^ 32) (executed : finishDestination id before.construction = .ok () after) :
    ∃ storage, after.storage[ready.destination.storage]? = some storage ∧
      after.destinations[id]? = some { ready.destination with progress := .built count } ∧
      SampledRunBacking layout storage.bytes ⟨ready.destination.capability.start + 4, count, .int .u8⟩ := by
  have element : ready.element = .int .u8 := by
    simpa only [elementType, Option.some.injEq] using ready.elementType.symm
  have scan := ready.scan
  rw [element] at scan
  have ending := byte_elementsEnd_exact ready.fuel layout ready.storage.bytes count
    (destinationPayloadStart ready.destination) ready.destination.writeEnd scan
  have start : destinationPayloadStart ready.destination = ready.destination.capability.start + 4 := by
    simp only [destinationPayloadStart, packed, request, beq_self_eq_true, Bool.true_and, ↓reduceIte]
  rw [start] at ending
  have bounded : ready.destination.capability.start + 4 + count ≤ ready.storage.bytes.size := by
    have bound := ready.bounded
    omega
  obtain ⟨storage, stored, _, size, present⟩ := finishDestination_packed_count before.construction after id
    ready.destination ready.storage count ready.present ready.bytes ready.opened packed request (by omega) fits executed
  refine ⟨storage, stored, present, ⟨count + 1, ready.destination.capability.start + 4 + count, ?_, ?_, ?_⟩⟩
  · have bound : ready.destination.capability.start + 4 + count * 1 ≤ storage.bytes.size := by
      rw [size]
      simpa only [Nat.mul_one] using bounded
    simpa only [Nat.mul_one] using elementsEnd_fixed layout storage.bytes (.int .u8) 1 rfl count
      (ready.destination.capability.start + 4) bound
  · change ready.destination.capability.start + 4 ≤ ready.destination.capability.start + 4 + count
    omega
  · rw [size]; exact bounded

theorem buildExpr_byteOwner_geometry (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (bytes : List UInt8) (origin : Goose.Core.OriginId) (id count : Nat) (before after : ExecutionState)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (fits : count + bytes.length < 2 ^ 32) (valid : DestinationLifecycleInvariant before.construction)
    (current : destinationCurrent before.construction id = .ok id)
    (executed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    ∃ destination storage, after.construction.destinations[id]? = some destination ∧
      after.construction.storage[destination.storage]? = some storage ∧
      destination.layout = .packed ∧ destination.capability.request = .value ∧
      destination.capability.logicalType = .varr (.int .u8) ∧
      destination.backing = ready.destination.backing ∧ destination.use = ready.destination.use ∧
      destination.progress = .built (count + bytes.length) ∧
      SampledRunBacking config.layout storage.bytes ⟨destination.capability.start + 4, count + bytes.length, .int .u8⟩ := by
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
    obtain ⟨following, layoutSame, capabilitySame, backingSame, useSame⟩ :=
      bytes_writeLoop_open_backing bytes config.layout origin id count before middle ready current loop
    have packed' : following.destination.layout = .packed := layoutSame.trans packed
    have request' : following.destination.capability.request = .value := by rw [capabilitySame]; exact request
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
      obtain ⟨storage, stored, found, interval⟩ := finished_byteOwner_geometry config.layout middle final id
        (count + bytes.length) following packed' request' fits finished
      exact ⟨{ following.destination with progress := .built (count + bytes.length) }, storage, found, stored,
        packed', request', following.logicalType, backingSame, useSame, rfl, interval⟩

theorem publish_direct_packed_backing (layout : LayoutEnv) (origin : Goose.Core.OriginId)
    (id storageId count : Nat) (before after : ExecutionState)
    (destination : PendingDestination) (storage : ReceivingStorage)
    (present : before.construction.destinations[id]? = some destination)
    (stored : before.construction.storage[storageId]? = some storage)
    (backing : destination.backing = .direct storageId)
    (progress : destination.progress = .built count) (use : destination.use = .receiver)
    (packed : destination.layout = .packed)
    (interval : SampledRunBacking layout storage.bytes
      ⟨destination.capability.start + (if destination.layout == .packed && destination.capability.request == .value then 4 else 0),
        count, .int .u8⟩)
    (ty : destination.capability.logicalType = .varr (.int .u8))
    (executed : publishCarriers origin [.completed id] before = .ok () after) :
    ∃ value, storedDestination id after = .ok value after ∧ StoredValueBacking layout after value ∧
      value.storage = storageId ∧ value.destination = some id := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  simp only [publishCarriers, List.mapM_cons, List.mapM_nil, bind, pure, List.filterMap_cons,
    List.filterMap_nil, _root_.id, liftConstruction] at executed
  simp only [publishOperation, ConstructionM.get, bind] at executed
  cases checked : preflightPublication before.construction [id] with
  | error reason => simp only [checked, ConstructionM.fail] at executed; cases executed
  | ok result =>
    cases result
    simp only [checked, List.forIn_cons, List.forIn_nil, bind, pure, publishReady_transition,
      lookupDestination_result, present, progress, use, backing, DestinationBacking.receiverStorage,
      lookupStorage_result, stored, packed, replaceStorage_result, replaceDestination_result,
      storageInside, inside, ↓reduceIte, emit_result, ExecutionStep.ok.injEq,
      true_and] at executed
    subst after
    let published := { destination with progress := .published count, backing := .direct storageId, writeEnd := destination.capability.start + (destination.writeEnd - destination.capability.start) }
    let value : StoredValue := ⟨storageId, destination.capability.start, .varr (.int .u8), count, some id, none, [], count⟩
    have row : (before.construction.destinations.set! id published)[id]? = some published :=
      Array.getElem?_setIfInBounds_self_of_lt inside
    have bytes : (before.construction.storage.set! storageId { storage with publishedCount := count })[storageId]? =
        some { storage with publishedCount := count } := Array.getElem?_setIfInBounds_self_of_lt storageInside
    refine ⟨value, ?_, ?_, rfl, rfl⟩
    · simp [storedDestination, getDestination, EvalM.get, bind, pure,
        inside, DestinationBacking.receiverStorage,
        progressCount, ty, value]
    · refine .named id { storage with publishedCount := count } published count bytes rfl ?_ ?_ ?_ ?_ ?_
        (.int .u8) rfl ?_
      · simpa only [published, packed, use, backing] using row
      · rfl
      · simpa only [published, value] using ty.symm
      · rfl
      · rfl
      · simpa [published, value, storedWrittenRun, packed] using interval

theorem allocated_published_byteOwner_backing (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (before allocated built final : ExecutionState) (id : Nat)
    (ambient : Goose.Proofs.ConstructionExecutionOwnership.OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout environment.act (.varr (.int .u8)) .value origin none (some bytes.length) before =
      .ok id allocated)
    (constructed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) allocated =
      .ok () built)
    (published : publishCarriers origin [.completed id] built = .ok () final) :
    ∃ value, storedDestination id final = .ok value final ∧
      StoredValueBacking config.layout final value ∧ value.storage = before.construction.storage.size ∧
      value.destination = some id := by
  obtain ⟨ready⟩ := newDestination_initial_backing config.layout environment.act (.varr (.int .u8)) .value
    origin (some bytes.length) before allocated id (.int .u8) rfl created
  obtain ⟨initial, initialPresent, packed, request, backing, use⟩ := newDestination_byteOwner_packed_value config.layout
    environment.act origin (some bytes.length) before allocated id created
  have same : initial = ready.destination := Option.some.inj (initialPresent.symm.trans ready.present)
  subst initial
  have allocatedWorld := newDestination_acceptedWorld config environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) initialized before allocated id ambient types live regions pending world created
  have current := newDestination_current_self config initialized environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) before allocated id ambient types live regions pending world created
  have fits := newDestination_byteOwner_count_bound config.layout environment.act origin bytes.length before allocated id created
  obtain ⟨destination, storage, present, stored, packed', request', ty, direct, receiver, progress, interval⟩ :=
    buildExpr_byteOwner_geometry fuel config environment bytes origin id 0 allocated built ready packed request
      (by simpa using fits) allocatedWorld.ownership.source.structural.1.1.1 current constructed
  have direct' : destination.backing = .direct before.construction.storage.size := direct.trans backing
  have receiver' : destination.use = .receiver := receiver.trans use
  have stored' : built.construction.storage[before.construction.storage.size]? = some storage := by
    simpa only [PendingDestination.storage, direct', DestinationBacking.writeStorage] using stored
  have interval' : SampledRunBacking config.layout storage.bytes
      ⟨destination.capability.start + (if destination.layout == .packed && destination.capability.request == .value then 4 else 0),
        bytes.length, .int .u8⟩ := by
    simpa only [packed', request', beq_self_eq_true, Bool.true_and, ↓reduceIte, Nat.zero_add] using interval
  obtain ⟨value, sampled, backed, identity, named⟩ := publish_direct_packed_backing config.layout origin id
    before.construction.storage.size bytes.length built final destination storage present stored' direct'
    (by simpa only [Nat.zero_add] using progress) receiver' packed' interval' ty published
  exact ⟨value, sampled, backed, identity, named⟩

#print axioms finished_byteOwner_geometry
#print axioms buildExpr_byteOwner_geometry
#print axioms publish_direct_packed_backing
#print axioms allocated_published_byteOwner_backing

end Goose.Proofs.ConstructionAcceptedExecution
