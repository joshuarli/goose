import Goose.Proofs.ConstructionByteWriteStopped

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionStorage
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem finishPacked_fault_unchanged (state final : ConstructionState) (id count : Nat)
    (row : PendingDestination) (present : state.destinations[id]? = some row)
    (opened : row.progress = .open count) (packed : row.layout = .packed)
    (request : row.capability.request = .value) (reason : ConstructionFault)
    (executed : finishDestination id state = .fault reason final) : final = state := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  simp only [finishDestination, writableDestination_result, present, bind] at executed
  cases allowed : destinationCanWrite state id with
  | false => simp only [allowed, ConstructionResult.fault.injEq] at executed; exact executed.2.symm
  | true =>
    simp only [allowed, opened, packed, hasPrefix_result, request, beq_self_eq_true, Bool.and_self,
      ↓reduceIte, lookupStorage_result] at executed
    cases stored : state.storage[row.storage]? with
    | none => simp only [stored, ConstructionResult.fault.injEq] at executed; exact executed.2.symm
    | some storage =>
      have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
      simp only [stored, replaceStorage_result, replaceDestination_result, storageInside, inside, ↓reduceIte] at executed
      cases executed

theorem bytes_finish_stopped_world_with_frame (bytes : List UInt8) (origin : Goose.Core.OriginId)
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
      (freshReceivingRegion before before.construction.destinations.size :: regions) pending ∧ Nonempty (FreshDestinationFrame before after) := by
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
    refine ⟨⟨⟨inherited.ownership, inherited.globals, inherited.globalTypes, inherited.layouts, inherited.typeFrontier,
      inherited.syntheticFrontier, inherited.heap, inherited.objectsRegistered, inherited.ordinalsRegistered,
      inherited.backing, ?_, inherited.carriers⟩, inherited.globalLive⟩, ⟨next⟩⟩
    intro region member
    rcases List.mem_cons.mp member with same | member
    · subst region; exact protection
    · exact inherited.protections region member

theorem bytes_finish_stopped_world (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (config : EvalConfig) (accepted : AcceptedModule config) (sourceFrame : ConstructionSourceFrame)
    (before state middle after : ExecutionState) (frame : FreshDestinationFrame before state) (count : Nat)
    (ready : OpenDestinationBacking config.layout state before.construction.destinations.size (.varr (.int .u8)) count)
    (direct : frame.row.backing = .direct before.construction.storage.size)
    (packed : frame.row.layout = .packed) (request : frame.row.capability.request = .value)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config sourceFrame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted sourceFrame before types) (valid : OwnershipSourceState state.construction)
    (current : destinationCurrent state.construction before.construction.destinations.size =
      .ok before.construction.destinations.size)
    (loop : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin before.construction.destinations.size (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) state = .ok PUnit.unit middle)
    (stop : Goose.Core.Stop)
    (finished : receivingAction origin before.construction.destinations.size finishDestination middle = .stop stop after) :
    AcceptedWorld config sourceFrame.initialized after ambient types live
      (freshReceivingRegion before before.construction.destinations.size :: regions) pending ∧
      AcceptedFrame config accepted sourceFrame after types := by
  obtain ⟨preserved, ⟨frameAfter⟩⟩ := bytes_finish_stopped_world_with_frame bytes origin config sourceFrame.initialized sourceFrame.interpretation.environment before state middle after frame count ready direct packed request ambient types live regions pending world valid current loop stop finished
  exact ⟨preserved, frameAfter.acceptedFrame source⟩

#print axioms finishPacked_fault_unchanged
#print axioms bytes_finish_stopped_world

end Goose.Proofs.ConstructionAcceptedExecution
