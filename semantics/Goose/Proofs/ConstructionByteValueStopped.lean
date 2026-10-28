import Goose.Proofs.ConstructionBytePublishStopped
import Goose.Proofs.ConstructionByteNoTimeout
import Goose.Proofs.ConstructionAcceptedByteStatement

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionStorage
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem evalValue_byteOwner_stopped_afterAllocation (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (sourceFrame : ConstructionSourceFrame) (before allocated after : ExecutionState)
    (bytes : List UInt8) (origin : Goose.Core.OriginId) (id : Nat) (stop : Goose.Core.Stop)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config sourceFrame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted sourceFrame before types)
    (created : newDestination config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin none
      (some bytes.length) before = .ok id allocated)
    (executed : evalValue (fuel + 2) config sourceFrame.interpretation.environment (.bytes (.varr (.int .u8)) bytes origin) before =
      .stop stop after) :
    AcceptedWorld config sourceFrame.initialized after ambient types live (freshReceivingRegion before id :: regions) pending ∧
      AcceptedFrame config accepted sourceFrame after types := by
  have created' := created
  simp only [EvalConfig.layout] at created'
  simp only [evalValue, Ty.nonfixed, constructLocal, producerCount?, literalCount, bind, ↓reduceIte, created'] at executed
  cases constructed : buildExpr (fuel + 1) config sourceFrame.interpretation.environment id
      (.bytes (.varr (.int .u8)) bytes origin) allocated with
  | stop reason state =>
    simp only [constructed, ExecutionStep.stop.injEq] at executed
    obtain ⟨rfl, rfl⟩ := executed
    exact buildExpr_byteOwner_stopped_world fuel config accepted sourceFrame before allocated state bytes origin origin id reason
      ambient types live regions pending world source created constructed
  | escape address carriers state =>
    have localAction := buildExpr_byteOwner_local fuel config sourceFrame.interpretation.environment id (.varr (.int .u8)) bytes origin allocated
    rw [constructed] at localAction
    cases localAction
  | jump target kind state =>
    have localAction := buildExpr_byteOwner_local fuel config sourceFrame.interpretation.environment id (.varr (.int .u8)) bytes origin allocated
    rw [constructed] at localAction
    cases localAction
  | ok result built =>
    cases result
    simp only [constructed] at executed
    have freshId := newDestination_fresh_id config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin
      (some bytes.length) before allocated id created
    subst id
    let id := before.construction.destinations.size
    change buildExpr (fuel + 1) config sourceFrame.interpretation.environment id
      (.bytes (.varr (.int .u8)) bytes origin) allocated = .ok () built at constructed
    obtain ⟨frame⟩ := newDestination_fresh_frame config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin
      (some bytes.length) before allocated id world.ownership.source.structural.1.1.1 created
    obtain ⟨ready⟩ := newDestination_initial_backing config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin
      (some bytes.length) before allocated id (.int .u8) rfl created
    obtain ⟨row, present, packed, request, direct, receiver⟩ := newDestination_byteOwner_packed_value config.layout
      sourceFrame.interpretation.environment.act origin (some bytes.length) before allocated id created
    have framePresent : allocated.construction.destinations[id]? = some frame.row := by
      rw [frame.destinations]; exact Array.getElem?_push_size
    have same : row = frame.row := Option.some.inj (present.symm.trans framePresent)
    subst row
    have allocatedWorld := newDestination_acceptedWorld config sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin
      (some bytes.length) sourceFrame.initialized before allocated id ambient types live regions pending world created
    have current := newDestination_current_self config sourceFrame.initialized sourceFrame.interpretation.environment.act (.varr (.int .u8))
      .value origin (some bytes.length) before allocated id ambient types live regions pending world created
    obtain ⟨builtFrame, _⟩ := buildExpr_byteOwner_freshFrame fuel config sourceFrame.interpretation.environment bytes origin before allocated built
      frame before.construction.storage.size 0 ready direct rfl packed request allocatedWorld.ownership.source.structural.1.1.1 current constructed
    have currentBuilt := frame.same_current builtFrame id current
    have fits := newDestination_byteOwner_count_bound config.layout sourceFrame.interpretation.environment.act origin bytes.length before allocated id created
    have readySame : ready.destination = frame.row := Option.some.inj (ready.present.symm.trans framePresent)
    obtain ⟨builtRow, storage, builtPresent, stored, _, _, _, _, _, builtProgress, _⟩ :=
      buildExpr_byteOwner_geometry fuel config sourceFrame.interpretation.environment bytes origin id 0 allocated built ready
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
      exact allocated_byteOwner_publishStop_world fuel config accepted sourceFrame before allocated built state bytes origin origin id reason
        ambient types live regions pending world source created constructed published
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
      simp only [published', pure, carrierValue, bind] at executed
      obtain ⟨_, _, stored, sampled, _, _, _, _⟩ := allocated_published_byteOwner_world fuel config sourceFrame.initialized
        sourceFrame.interpretation.environment bytes origin origin before allocated built final id ambient types live regions pending
        world created constructed published
      dsimp only [id] at sampled
      simp only [sampled, reduceCtorEq] at executed

#print axioms evalValue_byteOwner_stopped_afterAllocation

end Goose.Proofs.ConstructionAcceptedExecution
