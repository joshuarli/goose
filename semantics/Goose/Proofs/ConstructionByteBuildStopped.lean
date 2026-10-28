import Goose.Proofs.ConstructionByteFinishStopped
import Goose.Proofs.ConstructionByteNoTimeout

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionStorage
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem buildExpr_byteOwner_stopped_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (sourceFrame : ConstructionSourceFrame) (before allocated after : ExecutionState)
    (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId) (id : Nat) (stop : Goose.Core.Stop)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config sourceFrame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted sourceFrame before types)
    (created : newDestination config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin none
      (some bytes.length) before = .ok id allocated)
    (executed : buildExpr (fuel + 1) config sourceFrame.interpretation.environment id
      (.bytes (.varr (.int .u8)) bytes bytesOrigin) allocated = .stop stop after) :
    AcceptedWorld config sourceFrame.initialized after ambient types live (freshReceivingRegion before id :: regions) pending ∧
      AcceptedFrame config accepted sourceFrame after types := by
  have freshId := newDestination_fresh_id config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) before allocated id created
  subst id
  let id := before.construction.destinations.size
  change buildExpr (fuel + 1) config sourceFrame.interpretation.environment id
    (.bytes (.varr (.int .u8)) bytes bytesOrigin) allocated = .stop stop after at executed
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
  have readySame : ready.destination = frame.row := Option.some.inj (ready.present.symm.trans framePresent)
  have opened : frame.row.progress = .open 0 := by rw [← readySame]; exact ready.opened
  have allocatedWorld := newDestination_acceptedWorld config sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) sourceFrame.initialized before allocated id ambient types live regions pending world created
  have current := newDestination_current_self config sourceFrame.initialized sourceFrame.interpretation.environment.act (.varr (.int .u8))
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
    exact bytes_writeLoop_stopped_world bytes bytesOrigin config accepted sourceFrame before allocated middle frame 0 direct opened
      ambient types live regions pending world source allocatedWorld.ownership.source current reason loopStopped
  | ok result middle =>
    cases result
    have ran' := ran
    simp only [loop, bind] at ran'
    simp only [buildExpr, liftConstruction, renewal, bind, protectDestination, ran'] at executed
    cases finished : receivingAction bytesOrigin id finishDestination middle with
    | stop reason final =>
      simp only [finished, ExecutionStep.stop.injEq] at executed
      obtain ⟨rfl, rfl⟩ := executed
      exact bytes_finish_stopped_world bytes bytesOrigin config accepted sourceFrame before allocated middle final frame 0 ready direct
        packed request ambient types live regions pending world source allocatedWorld.ownership.source current ran reason finished
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

#print axioms buildExpr_byteOwner_stopped_world

end Goose.Proofs.ConstructionAcceptedExecution
