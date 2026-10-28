import Goose.Proofs.ConstructionBytePublishStopped
import Goose.Proofs.ConstructionByteNoTimeout
import Goose.Proofs.ConstructionAcceptedByteStatement
import Goose.Proofs.ConstructionByteStorageWorld

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionStorage
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem constructLocal_byteOwner_stopped_afterAllocation_with_frame (fuel : Nat) (config : EvalConfig) (initialized : Nat) (environment : RuntimeActivation) (before allocated after : ExecutionState)
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
    AcceptedWorld config initialized after ambient types live (freshReceivingRegion before id :: regions) pending ∧ Nonempty (FreshDestinationFrame before after) := by
  have created' := created
  simp only [EvalConfig.layout] at created'
  simp only [constructLocal, producerCount?, literalCount, bind, created'] at executed
  cases constructed : buildExpr (fuel + 1) config environment id
      (.bytes (.varr (.int .u8)) bytes bytesOrigin) allocated with
  | stop reason state =>
    simp only [constructed, ExecutionStep.stop.injEq] at executed
    obtain ⟨rfl, rfl⟩ := executed
    exact buildExpr_byteOwner_stopped_world_with_frame fuel config initialized environment before allocated state bytes origin bytesOrigin id reason
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
      exact allocated_byteOwner_publishStop_world_with_frame fuel config initialized environment before allocated built state bytes origin bytesOrigin id reason
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

theorem constructLocal_byteOwner_stopped_afterAllocation (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (sourceFrame : ConstructionSourceFrame) (before allocated after : ExecutionState)
    (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId) (id : Nat) (stop : Goose.Core.Stop)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config sourceFrame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted sourceFrame before types)
    (created : newDestination config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin none
      (some bytes.length) before = .ok id allocated)
    (executed : constructLocal ⟨config.module, sourceFrame.interpretation.environment.vars⟩ sourceFrame.interpretation.environment.act
      (.varr (.int .u8)) origin (.bytes (.varr (.int .u8)) bytes bytesOrigin)
      (fun destination => buildExpr (fuel + 1) config sourceFrame.interpretation.environment destination
        (.bytes (.varr (.int .u8)) bytes bytesOrigin)) before = .stop stop after) :
    AcceptedWorld config sourceFrame.initialized after ambient types live (freshReceivingRegion before id :: regions) pending ∧
      AcceptedFrame config accepted sourceFrame after types := by
  obtain ⟨preserved, ⟨frameAfter⟩⟩ := constructLocal_byteOwner_stopped_afterAllocation_with_frame fuel config sourceFrame.initialized sourceFrame.interpretation.environment before allocated after bytes origin bytesOrigin id stop ambient types live regions pending world created executed
  exact ⟨preserved, frameAfter.acceptedFrame source⟩

theorem constructLocal_byteOwner_stopped_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (sourceFrame : ConstructionSourceFrame) (before after : ExecutionState)
    (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId) (stop : Goose.Core.Stop)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config sourceFrame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted sourceFrame before types)
    (executed : constructLocal ⟨config.module, sourceFrame.interpretation.environment.vars⟩ sourceFrame.interpretation.environment.act
      (.varr (.int .u8)) origin (.bytes (.varr (.int .u8)) bytes bytesOrigin)
      (fun destination => buildExpr fuel config sourceFrame.interpretation.environment destination
        (.bytes (.varr (.int .u8)) bytes bytesOrigin)) before = .stop stop after) :
    ∃ nextRegions, AcceptedWorld config sourceFrame.initialized after ambient types live nextRegions pending ∧
      AcceptedFrame config accepted sourceFrame after types := by
  cases created : newDestination config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin none
      (some bytes.length) before with
  | stop reason final =>
    have created' := created
    simp only [EvalConfig.layout] at created'
    simp only [constructLocal, producerCount?, literalCount, bind, created', ExecutionStep.stop.injEq] at executed
    obtain ⟨rfl, rfl⟩ := executed
    exact ⟨regions, newDestination_byteOwner_stopped_world config sourceFrame.initialized _ origin bytes.length before final reason
      ambient types live regions pending world created,
      newDestination_byteOwner_stopped_frame _ origin bytes.length reason source created⟩
  | escape address carriers final =>
    have localAction := newByteDestination_local config sourceFrame.interpretation.environment origin bytes.length before
    rw [created] at localAction
    cases localAction
  | jump target kind final =>
    have localAction := newByteDestination_local config sourceFrame.interpretation.environment origin bytes.length before
    rw [created] at localAction
    cases localAction
  | ok destination allocated =>
    cases fuel with
    | zero =>
      have created' := created
      simp only [EvalConfig.layout] at created'
      simp only [constructLocal, producerCount?, literalCount, bind, created', buildExpr, timeout, EvalM.stop,
        ExecutionStep.stop.injEq] at executed
      obtain ⟨rfl, rfl⟩ := executed
      have allocatedWorld := newDestination_acceptedWorld config sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin
        (some bytes.length) sourceFrame.initialized before allocated destination ambient types live regions pending world created
      obtain ⟨freshFrame⟩ := newDestination_fresh_frame config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin
        (some bytes.length) before allocated destination world.ownership.source.structural.1.1.1 created
      exact ⟨freshReceivingRegion before destination :: regions, allocatedWorld, freshFrame.acceptedFrame source⟩
    | succ fuel =>
      exact ⟨freshReceivingRegion before destination :: regions,
        constructLocal_byteOwner_stopped_afterAllocation fuel config accepted sourceFrame before allocated after bytes origin bytesOrigin
          destination stop ambient types live regions pending world source created executed⟩

#print axioms constructLocal_byteOwner_stopped_afterAllocation
#print axioms constructLocal_byteOwner_stopped_world

end Goose.Proofs.ConstructionAcceptedExecution
