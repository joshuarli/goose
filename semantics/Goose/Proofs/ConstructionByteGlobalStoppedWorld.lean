import Goose.Proofs.ConstructionByteLocalStopped
import Goose.Proofs.ConstructionAcceptedByteGlobal

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionStorage
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem bytes_writeLoop_stopped_world_global (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (config : EvalConfig) (initialized : Nat) (environment : RuntimeActivation)
    (before state after : ExecutionState) (frame : FreshDestinationFrame before state) (count : Nat)
    (direct : frame.row.backing = .direct before.construction.storage.size) (opened : frame.row.progress = .open count)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (valid : OwnershipSourceState state.construction)
    (current : destinationCurrent state.construction before.construction.destinations.size =
      .ok before.construction.destinations.size) (stop : Goose.Core.Stop)
    (executed : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin before.construction.destinations.size (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) state = .stop stop after) :
    AcceptedWorld config initialized after ambient types live
      (freshReceivingRegion before before.construction.destinations.size :: regions) pending := by
  obtain ⟨finalFrame, finalDirect, finalSource⟩ := bytes_writeLoop_stopped_invariants bytes origin before state after
    frame before.construction.storage.size count direct rfl opened valid current stop executed
  have inherited := finalFrame.acceptedWorld config initialized ambient types live regions pending world finalSource
  have protection := finalFrame.freshProtection config.layout live world.backing finalDirect
  refine ⟨⟨inherited.ownership, inherited.globals, inherited.globalTypes, inherited.layouts, inherited.typeFrontier,
    inherited.syntheticFrontier, inherited.heap, inherited.objectsRegistered, inherited.ordinalsRegistered,
    inherited.backing, ?_, inherited.carriers⟩, inherited.globalLive⟩
  intro region member
  rcases List.mem_cons.mp member with same | member
  · subst region
    exact protection
  · exact inherited.protections region member


theorem bytes_finish_stopped_world_global (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (config : EvalConfig) (initialized : Nat) (environment : RuntimeActivation)
    (before state middle after : ExecutionState) (frame : FreshDestinationFrame before state) (count : Nat)
    (ready : OpenDestinationBacking config.layout state before.construction.destinations.size (.varr (.int .u8)) count)
    (direct : frame.row.backing = .direct before.construction.storage.size)
    (packed : frame.row.layout = .packed) (request : frame.row.capability.request = .value)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (valid : OwnershipSourceState state.construction)
    (current : destinationCurrent state.construction before.construction.destinations.size =
      .ok before.construction.destinations.size)
    (loop : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin before.construction.destinations.size (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) state = .ok PUnit.unit middle)
    (stop : Goose.Core.Stop)
    (finished : receivingAction origin before.construction.destinations.size finishDestination middle = .stop stop after) :
    AcceptedWorld config initialized after ambient types live
      (freshReceivingRegion before before.construction.destinations.size :: regions) pending := by
  let id := before.construction.destinations.size
  have present : state.construction.destinations[id]? = some frame.row := by
    rw [frame.destinations]; exact Array.getElem?_push_size
  have same : ready.destination = frame.row := Option.some.inj (ready.present.symm.trans present)
  have opened : frame.row.progress = .open count := by rw [← same]; exact ready.opened
  obtain ⟨next, nextDirect⟩ := bytes_writeLoop_freshFrame bytes origin before state middle frame
    before.construction.storage.size count direct rfl opened current loop
  have nextValid := bytes_writeLoop_sourceState bytes origin id state middle frame.row count valid current present opened loop
  obtain ⟨_, _, current', row, n, rowPresent, rowOpened⟩ :=
    bytes_writeLoop_ownershipSource bytes origin id state middle frame.row count valid.structural.1.1.1 current present opened loop
  obtain ⟨following, sameLayout, sameCapability, _, _⟩ :=
    bytes_writeLoop_open_backing bytes config.layout origin id count state middle ready current loop
  have nextPresent : middle.construction.destinations[id]? = some next.row := by
    rw [next.destinations]; exact Array.getElem?_push_size
  have rowSame : next.row = following.destination := Option.some.inj (nextPresent.symm.trans following.present)
  have nextOpened : next.row.progress = .open (count + bytes.length) := by rw [rowSame]; exact following.opened
  have nextPacked : next.row.layout = .packed := by rw [rowSame, sameLayout, same]; exact packed
  have nextRequest : next.row.capability.request = .value := by rw [rowSame, sameCapability, same]; exact request
  have renewal : renewReceivingDestination id middle.construction = .ok id middle.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current', pure,
      lookupDestination_result, rowPresent, rowOpened]
  change receivingAction origin id finishDestination middle = .stop stop after at finished
  simp only [receivingAction, liftConstruction, renewal, bind] at finished
  cases result : finishDestination id middle.construction with
  | ok value final => simp only [result] at finished; cases finished
  | fault reason final =>
    have unchanged := finishPacked_fault_unchanged middle.construction final id (count + bytes.length)
      next.row nextPresent nextOpened nextPacked nextRequest reason result
    subst final
    simp only [result, ExecutionStep.stop.injEq] at finished
    obtain ⟨_, sameAfter⟩ := finished
    subst after
    have inherited := next.acceptedWorld config initialized ambient types live regions pending world nextValid
    have protection := next.freshProtection config.layout live world.backing nextDirect
    refine ⟨⟨inherited.ownership, inherited.globals, inherited.globalTypes, inherited.layouts, inherited.typeFrontier,
      inherited.syntheticFrontier, inherited.heap, inherited.objectsRegistered, inherited.ordinalsRegistered,
      inherited.backing, ?_, inherited.carriers⟩, inherited.globalLive⟩
    intro region member
    rcases List.mem_cons.mp member with same | member
    · subst region; exact protection
    · exact inherited.protections region member


theorem buildExpr_byteOwner_stopped_world_global (fuel : Nat) (config : EvalConfig) (initialized : Nat) (environment : RuntimeActivation) (before allocated after : ExecutionState)
    (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId) (id : Nat) (stop : Goose.Core.Stop)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout environment.act (.varr (.int .u8)) .value origin none
      (some bytes.length) before = .ok id allocated)
    (executed : buildExpr (fuel + 1) config environment id
      (.bytes (.varr (.int .u8)) bytes bytesOrigin) allocated = .stop stop after) :
    AcceptedWorld config initialized after ambient types live (freshReceivingRegion before id :: regions) pending := by
  have freshId := newDestination_fresh_id config.layout environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) before allocated id created
  subst id
  let id := before.construction.destinations.size
  change buildExpr (fuel + 1) config environment id
    (.bytes (.varr (.int .u8)) bytes bytesOrigin) allocated = .stop stop after at executed
  obtain ⟨frame⟩ := newDestination_fresh_frame config.layout environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) before allocated id world.ownership.source.structural.1.1.1 created
  obtain ⟨ready⟩ := newDestination_initial_backing config.layout environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) before allocated id (.int .u8) rfl created
  obtain ⟨row, present, packed, request, direct, receiver⟩ := newDestination_byteOwner_packed_value config.layout
    environment.act origin (some bytes.length) before allocated id created
  have framePresent : allocated.construction.destinations[id]? = some frame.row := by
    rw [frame.destinations]
    exact Array.getElem?_push_size
  have same : row = frame.row := Option.some.inj (present.symm.trans framePresent)
  subst row
  have readySame : ready.destination = frame.row := Option.some.inj (ready.present.symm.trans framePresent)
  have opened : frame.row.progress = .open 0 := by rw [← readySame]; exact ready.opened
  have allocatedWorld := newDestination_acceptedWorld config environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) initialized before allocated id ambient types live regions pending world created
  have current := newDestination_current_self config initialized environment.act (.varr (.int .u8))
    .value origin (some bytes.length) before allocated id ambient types live regions pending world created
  have renewal : renewReceivingDestination id allocated.construction = .ok id allocated.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure, lookupDestination_result, framePresent, opened]
  let loop : EvalM PUnit := forIn bytes PUnit.unit fun byte _ => do
    receivingAction bytesOrigin id (fun destination => writeElement destination ⟨#[byte]⟩)
    pure (.yield PUnit.unit)
  cases ran : loop allocated with
  | stop reason middle =>
    have loopStopped : loop allocated = .stop reason middle := ran
    have ran' := ran
    simp only [loop, bind] at ran'
    simp only [buildExpr, liftConstruction, renewal, bind, protectDestination, ran', ExecutionStep.stop.injEq] at executed
    obtain ⟨rfl, rfl⟩ := executed
    exact bytes_writeLoop_stopped_world_global bytes bytesOrigin config initialized environment before allocated middle frame 0 direct opened
      ambient types live regions pending world allocatedWorld.ownership.source current reason loopStopped
  | ok result middle =>
    cases result
    have ran' := ran
    simp only [loop, bind] at ran'
    simp only [buildExpr, liftConstruction, renewal, bind, protectDestination, ran'] at executed
    cases finished : receivingAction bytesOrigin id finishDestination middle with
    | stop reason final =>
      simp only [finished, ExecutionStep.stop.injEq] at executed
      obtain ⟨rfl, rfl⟩ := executed
      exact bytes_finish_stopped_world_global bytes bytesOrigin config initialized environment before allocated middle final frame 0 ready direct
        packed request ambient types live regions pending world allocatedWorld.ownership.source current ran reason finished
    | ok value final => simp only [finished] at executed; cases executed
    | escape address carriers final =>
      have localFinish : LocalConstructionAction (receivingAction bytesOrigin id finishDestination) := LocalConstructionAction.lift bytesOrigin _
      have impossible := localFinish middle
      rw [finished] at impossible
      cases impossible
    | jump target kind final =>
      have localFinish : LocalConstructionAction (receivingAction bytesOrigin id finishDestination) := LocalConstructionAction.lift bytesOrigin _
      have impossible := localFinish middle
      rw [finished] at impossible
      cases impossible
  | escape address carriers middle =>
    have localAction : LocalConstructionAction loop := bytes_writeLoop_local bytes bytesOrigin id
    have localLoop := localAction allocated
    rw [ran] at localLoop
    cases localLoop
  | jump target kind middle =>
    have localAction : LocalConstructionAction loop := bytes_writeLoop_local bytes bytesOrigin id
    have localLoop := localAction allocated
    rw [ran] at localLoop
    cases localLoop


theorem allocated_byteOwner_publishStop_world_global (fuel : Nat) (config : EvalConfig) (initialized : Nat) (environment : RuntimeActivation) (before allocated built after : ExecutionState)
    (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId) (id : Nat) (stop : Goose.Core.Stop)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout environment.act (.varr (.int .u8)) .value origin none
      (some bytes.length) before = .ok id allocated)
    (constructed : buildExpr (fuel + 1) config environment id
      (.bytes (.varr (.int .u8)) bytes bytesOrigin) allocated = .ok () built)
    (published : publishCarriers origin [.completed id] built = .stop stop after) :
    AcceptedWorld config initialized after ambient types live (freshReceivingRegion before id :: regions) pending := by
  have freshId := newDestination_fresh_id config.layout environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) before allocated id created
  subst id
  let id := before.construction.destinations.size
  obtain ⟨frame⟩ := newDestination_fresh_frame config.layout environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) before allocated id world.ownership.source.structural.1.1.1 created
  obtain ⟨ready⟩ := newDestination_initial_backing config.layout environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) before allocated id (.int .u8) rfl created
  obtain ⟨row, present, packed, request, direct, receiver⟩ := newDestination_byteOwner_packed_value config.layout
    environment.act origin (some bytes.length) before allocated id created
  have framePresent : allocated.construction.destinations[id]? = some frame.row := by
    rw [frame.destinations]
    exact Array.getElem?_push_size
  have same : row = frame.row := Option.some.inj (present.symm.trans framePresent)
  subst row
  have allocatedWorld := newDestination_acceptedWorld config environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) initialized before allocated id ambient types live regions pending world created
  have current := newDestination_current_self config initialized environment.act (.varr (.int .u8))
    .value origin (some bytes.length) before allocated id ambient types live regions pending world created
  obtain ⟨builtFrame, builtDirect⟩ := buildExpr_byteOwner_freshFrame fuel config environment bytes bytesOrigin
    before allocated built frame before.construction.storage.size 0 ready direct rfl packed request
    allocatedWorld.ownership.source.structural.1.1.1 current constructed
  have builtSource := buildExpr_bytes_sourceState fuel config environment id (.varr (.int .u8))
    bytes bytesOrigin allocated built ready.destination 0 allocatedWorld.ownership.source current ready.present ready.opened constructed
  have fits := newDestination_byteOwner_count_bound config.layout environment.act origin bytes.length
    before allocated id created
  have readySame : ready.destination = frame.row := Option.some.inj (ready.present.symm.trans framePresent)
  obtain ⟨builtRow, storage, builtPresent, stored, _, _, _, _, _, builtProgress, _⟩ :=
    buildExpr_byteOwner_geometry fuel config environment bytes bytesOrigin id 0 allocated built ready
      (by rw [readySame]; exact packed) (by rw [readySame]; exact request) (by simpa using fits)
      allocatedWorld.ownership.source.structural.1.1.1 current constructed
  have builtFramePresent : built.construction.destinations[id]? = some builtFrame.row := by
    rw [builtFrame.destinations]
    exact Array.getElem?_push_size
  have builtSame : builtRow = builtFrame.row := Option.some.inj (builtPresent.symm.trans builtFramePresent)
  subst builtRow
  have stored' : built.construction.storage[before.construction.storage.size]? = some storage := by
    simpa only [PendingDestination.storage, builtDirect, DestinationBacking.writeStorage] using stored
  change publishCarriers origin [.completed id] built = .stop stop after at published
  simp only [publishCarriers, List.mapM_cons, List.mapM_nil, bind, pure, List.filterMap_cons,
    List.filterMap_nil, _root_.id, liftConstruction] at published
  cases result : publishOperation [id] built.construction with
  | ok value final => simp only [result] at published; cases published
  | fault reason final =>
    have unchanged := publishPacked_fault_unchanged built.construction final id bytes.length before.construction.storage.size
      builtFrame.row builtFramePresent (by simpa using builtProgress) builtFrame.receiver builtDirect storage stored' reason result
    subst final
    simp only [result, ExecutionStep.stop.injEq] at published
    obtain ⟨_, sameAfter⟩ := published
    subst after
    have inherited := builtFrame.acceptedWorld config initialized ambient types live regions pending world builtSource
    have protection := builtFrame.freshProtection config.layout live world.backing builtDirect
    refine ⟨⟨inherited.ownership, inherited.globals, inherited.globalTypes, inherited.layouts, inherited.typeFrontier,
      inherited.syntheticFrontier, inherited.heap, inherited.objectsRegistered, inherited.ordinalsRegistered,
      inherited.backing, ?_, inherited.carriers⟩, inherited.globalLive⟩
    intro region member
    rcases List.mem_cons.mp member with same | member
    · subst region; exact protection
    · exact inherited.protections region member


theorem constructLocal_byteOwner_stopped_afterAllocation_global (fuel : Nat) (config : EvalConfig) (initialized : Nat) (environment : RuntimeActivation) (before allocated after : ExecutionState)
    (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId) (id : Nat) (stop : Goose.Core.Stop)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout environment.act (.varr (.int .u8)) .value origin none
      (some bytes.length) before = .ok id allocated)
    (executed : constructLocal ⟨config.module, environment.vars⟩ environment.act
      (.varr (.int .u8)) origin (.bytes (.varr (.int .u8)) bytes bytesOrigin)
      (fun destination => buildExpr (fuel + 1) config environment destination
        (.bytes (.varr (.int .u8)) bytes bytesOrigin)) before = .stop stop after) :
    AcceptedWorld config initialized after ambient types live (freshReceivingRegion before id :: regions) pending := by
  have created' := created
  simp only [EvalConfig.layout] at created'
  simp only [constructLocal, producerCount?, literalCount, bind, created'] at executed
  cases constructed : buildExpr (fuel + 1) config environment id
      (.bytes (.varr (.int .u8)) bytes bytesOrigin) allocated with
  | stop reason state =>
    simp only [constructed, ExecutionStep.stop.injEq] at executed
    obtain ⟨rfl, rfl⟩ := executed
    exact buildExpr_byteOwner_stopped_world_global fuel config initialized environment before allocated state bytes origin bytesOrigin id reason
      ambient types live regions pending world created constructed
  | escape address carriers state =>
    have localAction := buildExpr_byteOwner_local fuel config environment id (.varr (.int .u8)) bytes bytesOrigin allocated
    rw [constructed] at localAction
    cases localAction
  | jump target kind state =>
    have localAction := buildExpr_byteOwner_local fuel config environment id (.varr (.int .u8)) bytes bytesOrigin allocated
    rw [constructed] at localAction
    cases localAction
  | ok result built =>
    cases result
    simp only [constructed] at executed
    have freshId := newDestination_fresh_id config.layout environment.act (.varr (.int .u8)) .value origin
      (some bytes.length) before allocated id created
    subst id
    let id := before.construction.destinations.size
    change buildExpr (fuel + 1) config environment id
      (.bytes (.varr (.int .u8)) bytes bytesOrigin) allocated = .ok () built at constructed
    obtain ⟨frame⟩ := newDestination_fresh_frame config.layout environment.act (.varr (.int .u8)) .value origin
      (some bytes.length) before allocated id world.ownership.source.structural.1.1.1 created
    obtain ⟨ready⟩ := newDestination_initial_backing config.layout environment.act (.varr (.int .u8)) .value origin
      (some bytes.length) before allocated id (.int .u8) rfl created
    obtain ⟨row, present, packed, request, direct, receiver⟩ := newDestination_byteOwner_packed_value config.layout
      environment.act origin (some bytes.length) before allocated id created
    have framePresent : allocated.construction.destinations[id]? = some frame.row := by
      rw [frame.destinations]; exact Array.getElem?_push_size
    have same : row = frame.row := Option.some.inj (present.symm.trans framePresent)
    subst row
    have allocatedWorld := newDestination_acceptedWorld config environment.act (.varr (.int .u8)) .value origin
      (some bytes.length) initialized before allocated id ambient types live regions pending world created
    have current := newDestination_current_self config initialized environment.act (.varr (.int .u8))
      .value origin (some bytes.length) before allocated id ambient types live regions pending world created
    obtain ⟨builtFrame, _⟩ := buildExpr_byteOwner_freshFrame fuel config environment bytes bytesOrigin before allocated built
      frame before.construction.storage.size 0 ready direct rfl packed request allocatedWorld.ownership.source.structural.1.1.1 current constructed
    have currentBuilt := frame.same_current builtFrame id current
    have fits := newDestination_byteOwner_count_bound config.layout environment.act origin bytes.length before allocated id created
    have readySame : ready.destination = frame.row := Option.some.inj (ready.present.symm.trans framePresent)
    obtain ⟨builtRow, storage, builtPresent, stored, _, _, _, _, _, builtProgress, _⟩ :=
      buildExpr_byteOwner_geometry fuel config environment bytes bytesOrigin id 0 allocated built ready
        (by rw [readySame]; exact packed) (by rw [readySame]; exact request) (by simpa using fits)
        allocatedWorld.ownership.source.structural.1.1.1 current constructed
    have completed : completedReceivingDestination id built = .ok id built := by
      simp only [completedReceivingDestination, receivingDestination, liftConstruction, currentBuilt, bind,
        completedDestination, getDestination, EvalM.get, builtPresent, builtProgress, pure]
    have completed' := completed
    dsimp only [id] at completed'
    simp only [completed'] at executed
    cases published : publishCarriers origin [.completed id] built with
    | stop reason state =>
      have published' := published
      dsimp only [id] at published'
      simp only [published', ExecutionStep.stop.injEq] at executed
      obtain ⟨rfl, rfl⟩ := executed
      exact allocated_byteOwner_publishStop_world_global fuel config initialized environment before allocated built state bytes origin bytesOrigin id reason
        ambient types live regions pending world created constructed published
    | escape address carriers state =>
      have localAction := publishCompleted_local origin id built
      rw [published] at localAction
      cases localAction
    | jump target kind state =>
      have localAction := publishCompleted_local origin id built
      rw [published] at localAction
      cases localAction
    | ok value final =>
      cases value
      have published' := published
      dsimp only [id] at published'
      simp only [published', pure, reduceCtorEq] at executed


#print axioms bytes_writeLoop_stopped_world_global
#print axioms bytes_finish_stopped_world_global
#print axioms buildExpr_byteOwner_stopped_world_global
#print axioms allocated_byteOwner_publishStop_world_global
#print axioms constructLocal_byteOwner_stopped_afterAllocation_global

end Goose.Proofs.ConstructionAcceptedExecution
