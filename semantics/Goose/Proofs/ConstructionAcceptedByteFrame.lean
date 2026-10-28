import Goose.Proofs.ConstructionAcceptedByteSource

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionStorage

theorem FreshDestinationFrame.writeElement {before state : ExecutionState}
    (frame : FreshDestinationFrame before state) (bytes : ByteArray) (final : ConstructionState)
    (storageId : Nat) (direct : frame.row.backing = .direct storageId)
    (fresh : storageId = before.construction.storage.size)
    (executed : writeElement before.construction.destinations.size bytes state.construction = .ok () final) :
    ∃ next : FreshDestinationFrame before { state with construction := final }, next.row.backing = .direct storageId := by
  have transition := writeElement_transition before.construction.destinations.size bytes state.construction
  rw [executed] at transition
  cases transition with
  | written row storage count present stored opened =>
    have expected : state.construction.destinations[before.construction.destinations.size]? = some frame.row := by
      rw [frame.destinations]
      exact Array.getElem?_push_size
    have same : row = frame.row := Option.some.inj (present.symm.trans expected)
    subst row
    let updated := { frame.row with progress := .open (count + 1), writeEnd := frame.row.writeEnd + bytes.size }
    refine ⟨⟨?_, updated, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · have objects := congrArg ExecutionState.objects frame.outer
      have ordinals := congrArg ExecutionState.objectOrdinals frame.outer
      have acts := congrArg ExecutionState.nextAct frame.outer
      have scopes := congrArg ExecutionState.nextScope frame.outer
      have activations := congrArg ExecutionState.activations frame.outer
      have breaks := congrArg ExecutionState.breaks frame.outer
      simp only [ExecutionState.mk.injEq, true_and]
      exact ⟨objects, ordinals, acts, scopes, activations, breaks⟩
    · change (state.construction.destinations.set! before.construction.destinations.size updated) = _
      rw [frame.destinations]
      simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, Array.set_push]
    · exact frame.receiver
    · exact frame.successors
    · exact frame.tickets
    · intro id prior found
      have inside := (Array.getElem?_eq_some_iff.mp found).1
      have different : id ≠ frame.row.storage := by
        simp only [PendingDestination.storage, direct, DestinationBacking.writeStorage, fresh]
        omega
      change (state.construction.storage.set! frame.row.storage _)[id]? = some prior
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm different)]
      exact frame.storage id prior found
    · exact direct

theorem bytes_writeLoop_freshFrame (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (before state after : ExecutionState) (frame : FreshDestinationFrame before state) (storageId count : Nat)
    (direct : frame.row.backing = .direct storageId) (fresh : storageId = before.construction.storage.size)
    (opened : frame.row.progress = .open count)
    (current : destinationCurrent state.construction before.construction.destinations.size =
      .ok before.construction.destinations.size)
    (executed : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin before.construction.destinations.size (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) state = .ok PUnit.unit after) :
    ∃ next : FreshDestinationFrame before after, next.row.backing = .direct storageId := by
  induction bytes generalizing state count with
  | nil =>
    simp only [List.forIn_nil, pure, ExecutionStep.ok.injEq, true_and] at executed
    subst after
    exact ⟨frame, direct⟩
  | cons byte rest ih =>
    have present : state.construction.destinations[before.construction.destinations.size]? = some frame.row := by
      rw [frame.destinations]
      exact Array.getElem?_push_size
    have renewal : renewReceivingDestination before.construction.destinations.size state.construction =
        .ok before.construction.destinations.size state.construction := by
      simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
        lookupDestination_result, present, opened]
    simp only [List.forIn_cons, receivingAction, liftConstruction, renewal, bind] at executed
    cases written : writeElement before.construction.destinations.size ⟨#[byte]⟩ state.construction with
    | fault reason final => simp only [written] at executed; cases executed
    | ok value final =>
      cases value
      simp only [written, pure] at executed
      obtain ⟨next, nextDirect⟩ := frame.writeElement ⟨#[byte]⟩ final storageId direct fresh written
      have row' := writeElement_success_destination before.construction.destinations.size ⟨#[byte]⟩
        state.construction final frame.row count present opened written
      have nextPresent : final.destinations[before.construction.destinations.size]? = some next.row := by
        rw [next.destinations]
        exact Array.getElem?_push_size
      have same := Option.some.inj (nextPresent.symm.trans row'.1)
      have nextOpened : next.row.progress = .open (count + 1) := by rw [same]
      have indexing := writeElement_preserves_indexing before.construction.destinations.size ⟨#[byte]⟩ state.construction
      rw [written] at indexing
      simp only [ConstructionResult.finalState] at indexing
      have current' : destinationCurrent final before.construction.destinations.size =
          .ok before.construction.destinations.size := by
        rw [destinationCurrent_result, destinationCurrentSteps_same_indexing _ state.construction final indexing.1 indexing.2, indexing.1]
        simpa only [destinationCurrent_result] using current
      exact ih { state with construction := final } next (count + 1) nextDirect nextOpened current' executed

theorem FreshDestinationFrame.finishPacked {before state : ExecutionState}
    (frame : FreshDestinationFrame before state) (final : ConstructionState) (storageId count : Nat)
    (direct : frame.row.backing = .direct storageId) (fresh : storageId = before.construction.storage.size)
    (opened : frame.row.progress = .open count) (packed : frame.row.layout = .packed)
    (request : frame.row.capability.request = .value)
    (executed : finishDestination before.construction.destinations.size state.construction = .ok () final) :
    ∃ next : FreshDestinationFrame before { state with construction := final }, next.row.backing = .direct storageId := by
  have present : state.construction.destinations[before.construction.destinations.size]? = some frame.row := by
    rw [frame.destinations]
    exact Array.getElem?_push_size
  have inside : before.construction.destinations.size < state.construction.destinations.size := by
    rw [frame.destinations, Array.size_push]
    omega
  simp only [finishDestination, writableDestination_result, present, bind] at executed
  cases allowed : destinationCanWrite state.construction before.construction.destinations.size with
  | false => simp only [allowed] at executed; cases executed
  | true =>
    simp only [allowed, opened, packed, hasPrefix_result, request, beq_self_eq_true, Bool.and_self,
      ↓reduceIte, lookupStorage_result] at executed
    cases stored : state.construction.storage[frame.row.storage]? with
    | none => simp only [stored] at executed; cases executed
    | some storage =>
      have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
      simp only [stored, replaceStorage_result, replaceDestination_result, storageInside, inside, ↓reduceIte,
        ConstructionResult.ok.injEq, true_and] at executed
      subst final
      let updated := { frame.row with progress := .built count }
      refine ⟨⟨?_, updated, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · have objects := congrArg ExecutionState.objects frame.outer
        have ordinals := congrArg ExecutionState.objectOrdinals frame.outer
        have acts := congrArg ExecutionState.nextAct frame.outer
        have scopes := congrArg ExecutionState.nextScope frame.outer
        have activations := congrArg ExecutionState.activations frame.outer
        have breaks := congrArg ExecutionState.breaks frame.outer
        simp only [ExecutionState.mk.injEq, true_and]
        exact ⟨objects, ordinals, acts, scopes, activations, breaks⟩
      · change (state.construction.destinations.set! before.construction.destinations.size _) = _
        rw [frame.destinations]
        simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, Array.set_push, updated, packed]
      · exact frame.receiver
      · exact frame.successors
      · exact frame.tickets
      · intro id prior found
        have inside := (Array.getElem?_eq_some_iff.mp found).1
        have different : id ≠ frame.row.storage := by
          simp only [PendingDestination.storage, direct, DestinationBacking.writeStorage, fresh]
          omega
        change (state.construction.storage.set! frame.row.storage _)[id]? = some prior
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm different)]
        exact frame.storage id prior found
      · exact direct

theorem buildExpr_byteOwner_freshFrame (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (bytes : List UInt8) (origin : Goose.Core.OriginId) (before state after : ExecutionState)
    (frame : FreshDestinationFrame before state) (storageId count : Nat)
    (ready : OpenDestinationBacking config.layout state before.construction.destinations.size (.varr (.int .u8)) count)
    (direct : frame.row.backing = .direct storageId) (fresh : storageId = before.construction.storage.size)
    (packed : frame.row.layout = .packed) (request : frame.row.capability.request = .value)
    (valid : DestinationLifecycleInvariant state.construction)
    (current : destinationCurrent state.construction before.construction.destinations.size =
      .ok before.construction.destinations.size)
    (executed : buildExpr (fuel + 1) config environment before.construction.destinations.size
      (.bytes (.varr (.int .u8)) bytes origin) state = .ok () after) :
    ∃ next : FreshDestinationFrame before after, next.row.backing = .direct storageId := by
  let id := before.construction.destinations.size
  change destinationCurrent state.construction id = .ok id at current
  change buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) state = .ok () after at executed
  have present : state.construction.destinations[id]? = some frame.row := by
    rw [frame.destinations]
    exact Array.getElem?_push_size
  have same : ready.destination = frame.row := Option.some.inj (ready.present.symm.trans present)
  have opened : frame.row.progress = .open count := by rw [← same]; exact ready.opened
  have renewal : renewReceivingDestination id state.construction = .ok id state.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, present, opened]
  simp only [buildExpr, liftConstruction, renewal, bind] at executed
  have action := protectDestination_success origin id _ state after () executed
  cases loop : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin id (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) state with
  | stop reason middle => simp only [bind] at loop; rw [loop] at action; cases action
  | escape target carriers middle => simp only [bind] at loop; rw [loop] at action; cases action
  | jump target kind middle => simp only [bind] at loop; rw [loop] at action; cases action
  | ok value middle =>
    cases value
    obtain ⟨source, lifecycle, current', row, n, rowPresent, rowOpened⟩ :=
      bytes_writeLoop_ownershipSource bytes origin id state middle frame.row count valid current present opened loop
    obtain ⟨next, nextDirect⟩ := bytes_writeLoop_freshFrame bytes origin before state middle frame storageId count
      direct fresh opened current loop
    obtain ⟨following, sameLayout, sameCapability, _, _⟩ :=
      bytes_writeLoop_open_backing bytes config.layout origin id count state middle ready current loop
    have nextPresent : middle.construction.destinations[id]? = some next.row := by
      rw [next.destinations]
      exact Array.getElem?_push_size
    have rowSame : next.row = following.destination := Option.some.inj (nextPresent.symm.trans following.present)
    have nextOpened : next.row.progress = .open (count + bytes.length) := by rw [rowSame]; exact following.opened
    have nextPacked : next.row.layout = .packed := by rw [rowSame, sameLayout, same]; exact packed
    have nextRequest : next.row.capability.request = .value := by rw [rowSame, sameCapability, same]; exact request
    have renewal' : renewReceivingDestination id middle.construction = .ok id middle.construction := by
      simp only [renewReceivingDestination, ConstructionM.get, bind, current', pure,
        lookupDestination_result, rowPresent, rowOpened]
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
      exact next.finishPacked final storageId (count + bytes.length) nextDirect fresh nextOpened nextPacked nextRequest finished

theorem FreshDestinationFrame.publishPacked {before state after : ExecutionState}
    (frame : FreshDestinationFrame before state) (origin : Goose.Core.OriginId) (storageId count : Nat)
    (direct : frame.row.backing = .direct storageId) (fresh : storageId = before.construction.storage.size)
    (built : frame.row.progress = .built count) (packed : frame.row.layout = .packed)
    (executed : publishCarriers origin [.completed before.construction.destinations.size] state = .ok () after) :
    Nonempty (FreshDestinationFrame before after) := by
  let id := before.construction.destinations.size
  have present : state.construction.destinations[id]? = some frame.row := by
    rw [frame.destinations]
    exact Array.getElem?_push_size
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  change publishCarriers origin [.completed id] state = .ok () after at executed
  simp only [publishCarriers, List.mapM_cons, List.mapM_nil, bind, pure, List.filterMap_cons,
    List.filterMap_nil, _root_.id, liftConstruction] at executed
  simp only [publishOperation, ConstructionM.get, bind] at executed
  cases checked : preflightPublication state.construction [id] with
  | error reason => simp only [checked, ConstructionM.fail] at executed; cases executed
  | ok result =>
    cases result
    cases stored : state.construction.storage[storageId]? with
    | none =>
      simp only [checked, List.forIn_cons, bind, pure, publishReady_transition,
        lookupDestination_result, present, built, frame.receiver, direct, DestinationBacking.receiverStorage,
        lookupStorage_result, stored] at executed
      cases executed
    | some storage =>
      have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
      simp only [checked, List.forIn_cons, List.forIn_nil, bind, pure, publishReady_transition,
        lookupDestination_result, present, built, frame.receiver, direct, DestinationBacking.receiverStorage,
        lookupStorage_result, stored, packed, replaceStorage_result, replaceDestination_result,
        storageInside, inside, ↓reduceIte, emit_result, ExecutionStep.ok.injEq, true_and] at executed
      subst after
      let updated := { frame.row with progress := .published count, backing := .direct storageId, writeEnd := frame.row.capability.start + (frame.row.writeEnd - frame.row.capability.start) }
      refine ⟨⟨?_, updated, ?_, ?_, ?_, ?_, ?_⟩⟩
      · have objects := congrArg ExecutionState.objects frame.outer
        have ordinals := congrArg ExecutionState.objectOrdinals frame.outer
        have acts := congrArg ExecutionState.nextAct frame.outer
        have scopes := congrArg ExecutionState.nextScope frame.outer
        have activations := congrArg ExecutionState.activations frame.outer
        have breaks := congrArg ExecutionState.breaks frame.outer
        simp only [ExecutionState.mk.injEq, true_and]
        exact ⟨objects, ordinals, acts, scopes, activations, breaks⟩
      · change (state.construction.destinations.set! id _) = _
        rw [frame.destinations]
        simp [id, Array.set!_eq_setIfInBounds, Array.setIfInBounds, Array.set_push, updated, packed, frame.receiver]
      · exact frame.receiver
      · exact frame.successors
      · exact frame.tickets
      · intro old prior found
        have inside := (Array.getElem?_eq_some_iff.mp found).1
        have different : old ≠ storageId := by rw [fresh]; omega
        change (state.construction.storage.set! storageId _)[old]? = some prior
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm different)]
        exact frame.storage old prior found

theorem allocated_published_byteOwner_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
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
    AcceptedWorld config initialized final ambient types live regions pending ∧
      ∃ value, storedDestination id final = .ok value final ∧
        Goose.Proofs.ConstructionRepresentation.StoredValueBacking config.layout final value ∧
        value.storage = before.construction.storage.size ∧ value.destination = some id := by
  have freshId := newDestination_fresh_id config.layout environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) before allocated id created
  subst id
  obtain ⟨frame⟩ := newDestination_fresh_frame config.layout environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) before allocated before.construction.destinations.size world.ownership.source.structural.1.1.1 created
  obtain ⟨ready⟩ := newDestination_initial_backing config.layout environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) before allocated before.construction.destinations.size (.int .u8) rfl created
  obtain ⟨row, present, packed, request, direct, receiver⟩ := newDestination_byteOwner_packed_value config.layout
    environment.act origin (some bytes.length) before allocated before.construction.destinations.size created
  have framePresent : allocated.construction.destinations[before.construction.destinations.size]? = some frame.row := by
    rw [frame.destinations]; exact Array.getElem?_push_size
  have same : row = frame.row := Option.some.inj (present.symm.trans framePresent)
  subst row
  have allocatedWorld := newDestination_acceptedWorld config environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) initialized before allocated before.construction.destinations.size ambient types live regions pending world created
  have current := newDestination_current_self config initialized environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) before allocated before.construction.destinations.size ambient types live regions pending world created
  obtain ⟨builtFrame, builtDirect⟩ := buildExpr_byteOwner_freshFrame fuel config environment bytes origin before allocated built
    frame before.construction.storage.size 0 ready direct rfl packed request allocatedWorld.ownership.source.structural.1.1.1 current constructed
  have fits := newDestination_byteOwner_count_bound config.layout environment.act origin bytes.length before allocated
    before.construction.destinations.size created
  have readySame : ready.destination = frame.row := Option.some.inj (ready.present.symm.trans framePresent)
  obtain ⟨builtRow, storage, builtPresent, stored, builtPacked, _, _, _, _, builtProgress, interval⟩ :=
    buildExpr_byteOwner_geometry fuel config environment bytes origin before.construction.destinations.size 0 allocated built ready
      (by rw [readySame]; exact packed) (by rw [readySame]; exact request) (by simpa using fits)
      allocatedWorld.ownership.source.structural.1.1.1 current constructed
  have builtFramePresent : built.construction.destinations[before.construction.destinations.size]? = some builtFrame.row := by
    rw [builtFrame.destinations]; exact Array.getElem?_push_size
  have builtSame : builtRow = builtFrame.row := Option.some.inj (builtPresent.symm.trans builtFramePresent)
  subst builtRow
  obtain ⟨finalFrame⟩ := builtFrame.publishPacked origin before.construction.storage.size bytes.length builtDirect rfl
    (by simpa only [Nat.zero_add] using builtProgress) builtPacked published
  have source := allocated_published_byteOwner_sourceState fuel config initialized environment bytes origin before allocated built final
    before.construction.destinations.size ambient types live regions pending world created constructed published
  refine ⟨finalFrame.acceptedWorld config initialized ambient types live regions pending world source, ?_⟩
  exact allocated_published_byteOwner_backing fuel config initialized environment bytes origin before allocated built final
    before.construction.destinations.size ambient types live regions pending world created constructed published

#print axioms FreshDestinationFrame.writeElement
#print axioms bytes_writeLoop_freshFrame
#print axioms FreshDestinationFrame.finishPacked
#print axioms buildExpr_byteOwner_freshFrame
#print axioms FreshDestinationFrame.publishPacked
#print axioms allocated_published_byteOwner_world

end Goose.Proofs.ConstructionAcceptedExecution
