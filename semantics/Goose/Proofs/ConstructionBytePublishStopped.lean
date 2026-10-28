import Goose.Proofs.ConstructionByteBuildStopped

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionStorage
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem publishPacked_fault_unchanged (state final : ConstructionState) (id count storageId : Nat)
    (row : PendingDestination) (present : state.destinations[id]? = some row)
    (built : row.progress = .built count) (receiver : row.use = .receiver)
    (direct : row.backing = .direct storageId) (storage : ReceivingStorage)
    (stored : state.storage[storageId]? = some storage) (reason : ConstructionFault)
    (executed : publishOperation [id] state = .fault reason final) : final = state := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  simp only [publishOperation, ConstructionM.get, bind] at executed
  cases check : preflightPublication state [id] with
  | error fault => simp only [check, ConstructionM.fail, ConstructionResult.fault.injEq] at executed; exact executed.2.symm
  | ok value =>
    cases value
    simp only [check, List.forIn_cons, List.forIn_nil, publishReady_transition,
      lookupDestination_result, present, bind, built, receiver, direct, DestinationBacking.receiverStorage,
      lookupStorage_result, stored, replaceStorage_result, replaceDestination_result, storageInside, inside,
      ↓reduceIte, emit_result, pure, reduceCtorEq] at executed

theorem allocated_byteOwner_publishStop_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (sourceFrame : ConstructionSourceFrame) (before allocated built after : ExecutionState)
    (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId) (id : Nat) (stop : Goose.Core.Stop)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config sourceFrame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted sourceFrame before types)
    (created : newDestination config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin none
      (some bytes.length) before = .ok id allocated)
    (constructed : buildExpr (fuel + 1) config sourceFrame.interpretation.environment id
      (.bytes (.varr (.int .u8)) bytes bytesOrigin) allocated = .ok () built)
    (published : publishCarriers origin [.completed id] built = .stop stop after) :
    AcceptedWorld config sourceFrame.initialized after ambient types live (freshReceivingRegion before id :: regions) pending ∧
      AcceptedFrame config accepted sourceFrame after types := by
  have freshId := newDestination_fresh_id config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) before allocated id created
  subst id
  let id := before.construction.destinations.size
  obtain ⟨frame⟩ := newDestination_fresh_frame config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) before allocated id world.ownership.source.structural.1.1.1 created
  obtain ⟨ready⟩ := newDestination_initial_backing config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) before allocated id (.int .u8) rfl created
  obtain ⟨row, present, packed, request, direct, receiver⟩ := newDestination_byteOwner_packed_value config.layout
    sourceFrame.interpretation.environment.act origin (some bytes.length) before allocated id created
  have framePresent : allocated.construction.destinations[id]? = some frame.row := by
    rw [frame.destinations]
    exact Array.getElem?_push_size
  have same : row = frame.row := Option.some.inj (present.symm.trans framePresent)
  subst row
  have allocatedWorld := newDestination_acceptedWorld config sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) sourceFrame.initialized before allocated id ambient types live regions pending world created
  have current := newDestination_current_self config sourceFrame.initialized sourceFrame.interpretation.environment.act (.varr (.int .u8))
    .value origin (some bytes.length) before allocated id ambient types live regions pending world created
  obtain ⟨builtFrame, builtDirect⟩ := buildExpr_byteOwner_freshFrame fuel config sourceFrame.interpretation.environment bytes bytesOrigin
    before allocated built frame before.construction.storage.size 0 ready direct rfl packed request
    allocatedWorld.ownership.source.structural.1.1.1 current constructed
  have builtSource := buildExpr_bytes_sourceState fuel config sourceFrame.interpretation.environment id (.varr (.int .u8))
    bytes bytesOrigin allocated built ready.destination 0 allocatedWorld.ownership.source current ready.present ready.opened constructed
  have fits := newDestination_byteOwner_count_bound config.layout sourceFrame.interpretation.environment.act origin bytes.length
    before allocated id created
  have readySame : ready.destination = frame.row := Option.some.inj (ready.present.symm.trans framePresent)
  obtain ⟨builtRow, storage, builtPresent, stored, _, _, _, _, _, builtProgress, _⟩ :=
    buildExpr_byteOwner_geometry fuel config sourceFrame.interpretation.environment bytes bytesOrigin id 0 allocated built ready
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
    have inherited := builtFrame.acceptedWorld config sourceFrame.initialized ambient types live regions pending world builtSource
    have protection := builtFrame.freshProtection config.layout live world.backing builtDirect
    refine ⟨⟨⟨inherited.ownership, inherited.globals, inherited.globalTypes, inherited.layouts, inherited.typeFrontier,
      inherited.syntheticFrontier, inherited.heap, inherited.objectsRegistered, inherited.ordinalsRegistered,
      inherited.backing, ?_, inherited.carriers⟩, inherited.globalLive⟩, builtFrame.acceptedFrame source⟩
    intro region member
    rcases List.mem_cons.mp member with same | member
    · subst region; exact protection
    · exact inherited.protections region member

#print axioms publishPacked_fault_unchanged
#print axioms allocated_byteOwner_publishStop_world

end Goose.Proofs.ConstructionAcceptedExecution
