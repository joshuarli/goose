import Goose.Proofs.ConstructionAcceptedByteFrame
import Goose.Proofs.ConstructionAcceptedByteChecked

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionStorage
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem bytes_writeLoop_stopped_invariants (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (before state after : ExecutionState) (frame : FreshDestinationFrame before state) (storageId count : Nat)
    (direct : frame.row.backing = .direct storageId) (fresh : storageId = before.construction.storage.size)
    (opened : frame.row.progress = .open count)
    (valid : OwnershipSourceState state.construction)
    (current : destinationCurrent state.construction before.construction.destinations.size =
      .ok before.construction.destinations.size) (stop : Goose.Core.Stop)
    (executed : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin before.construction.destinations.size (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) state = .stop stop after) :
    ∃ next : FreshDestinationFrame before after,
      next.row.backing = .direct storageId ∧ OwnershipSourceState after.construction := by
  induction bytes generalizing state count with
  | nil => simp [List.forIn_nil, pure] at executed
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
    | fault reason final =>
      have transition := writeElement_transition before.construction.destinations.size ⟨#[byte]⟩ state.construction
      rw [written] at transition
      cases transition
      simp only [written] at executed
      cases reason <;> simp only [ExecutionStep.stop.injEq] at executed <;>
        obtain ⟨_, same⟩ := executed <;> subst after <;> exact ⟨frame, direct, valid⟩
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
      have extension := writeElement_ownership_source before.construction.destinations.size ⟨#[byte]⟩ state.construction valid.structural.1.1.1
      have nextValid := constructionPrimitive_sourceState_of_sourceExtension _ (.writeElement _ _) state.construction valid extension
      rw [written] at nextValid
      exact ih { state with construction := final } next (count + 1) nextDirect nextOpened nextValid current' executed

theorem FreshDestinationFrame.freshProtection {before after : ExecutionState} (frame : FreshDestinationFrame before after)
    (layout : LayoutEnv) (live : Goose.Core.RootInst → Prop) (backed : RootedBackingState layout before live)
    (direct : frame.row.backing = .direct before.construction.storage.size) :
    ReceivingProtection layout after live (freshReceivingRegion before before.construction.destinations.size) := by
  let id := before.construction.destinations.size
  have present : after.construction.destinations[id]? = some frame.row := by
    rw [frame.destinations]
    exact Array.getElem?_push_size
  have objects := congrArg ExecutionState.objects frame.outer
  have ordinals := congrArg ExecutionState.objectOrdinals frame.outer
  have extent : storageExtent before frame.row.storage = 0 := by
    simp only [PendingDestination.storage, direct, DestinationBacking.writeStorage, storageExtent,
      Array.getElem?_eq_none_iff.mpr (Nat.le_refl _), Option.map_none, Option.getD_none]
  refine ⟨⟨frame.row, present⟩, ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_, by simp [freshReceivingRegion], ?_, ?_⟩
  · intro root retained value found
    rw [objects] at found
    exact frame.value_backing layout value (backed.values root retained.1 value found)
  · intro root retained stored found
    rw [objects] at found
    rw [ordinals]
    exact backed.identities root retained.1 stored found
  · intro root retained value found stored occurrence
    rw [objects] at found
    have backing := (backed.values root retained.1 value found).occurrence_backing layout before value stored occurrence
    exact frame.stored_observation layout (storageExtent before) stored backing (backing.observation layout before stored)
  · intro row found
    have same : row = frame.row := Option.some.inj (found.symm.trans present)
    subst row
    simpa only [freshReceivingRegion, extent] using Nat.zero_le frame.row.rollbackEnd
  · intro row found
    have same : row = frame.row := Option.some.inj (found.symm.trans present)
    subst row
    simpa only [freshReceivingRegion, extent] using Nat.zero_le frame.row.capability.start
  · intro other member
    have same : other = id := by simpa only [freshReceivingRegion, List.mem_singleton] using member
    rw [same]
    exact (Array.getElem?_eq_some_iff.mp present).1
  · intro root retained outside value found stored occurrence namedId named
    rw [objects] at found
    have bound := ((backed.values root retained value found).occurrence_backing layout before value stored occurrence).named_bound
      layout before stored namedId named
    change namedId ∉ [id]
    simp only [List.mem_singleton]
    exact Nat.ne_of_lt bound

theorem bytes_writeLoop_stopped_world (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (config : EvalConfig) (accepted : AcceptedModule config) (sourceFrame : ConstructionSourceFrame)
    (before state after : ExecutionState) (frame : FreshDestinationFrame before state) (count : Nat)
    (direct : frame.row.backing = .direct before.construction.storage.size) (opened : frame.row.progress = .open count)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config sourceFrame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted sourceFrame before types) (valid : OwnershipSourceState state.construction)
    (current : destinationCurrent state.construction before.construction.destinations.size =
      .ok before.construction.destinations.size) (stop : Goose.Core.Stop)
    (executed : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin before.construction.destinations.size (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) state = .stop stop after) :
    AcceptedWorld config sourceFrame.initialized after ambient types live
      (freshReceivingRegion before before.construction.destinations.size :: regions) pending ∧
      AcceptedFrame config accepted sourceFrame after types := by
  obtain ⟨finalFrame, finalDirect, finalSource⟩ := bytes_writeLoop_stopped_invariants bytes origin before state after
    frame before.construction.storage.size count direct rfl opened valid current stop executed
  have inherited := finalFrame.acceptedWorld config sourceFrame.initialized ambient types live regions pending world finalSource
  have protection := finalFrame.freshProtection config.layout live world.backing finalDirect
  refine ⟨⟨⟨inherited.ownership, inherited.globals, inherited.globalTypes, inherited.layouts, inherited.typeFrontier,
    inherited.syntheticFrontier, inherited.heap, inherited.objectsRegistered, inherited.ordinalsRegistered,
    inherited.backing, ?_, inherited.carriers⟩, inherited.globalLive⟩, finalFrame.acceptedFrame source⟩
  intro region member
  rcases List.mem_cons.mp member with same | member
  · subst region
    exact protection
  · exact inherited.protections region member

theorem evalValue_byteOwner_writeStop_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (sourceFrame : ConstructionSourceFrame) (before allocated after : ExecutionState)
    (bytes : List UInt8) (origin : Goose.Core.OriginId) (id : Nat) (stop : Goose.Core.Stop)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config sourceFrame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted sourceFrame before types)
    (created : newDestination config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin none
      (some bytes.length) before = .ok id allocated)
    (stopped : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin id (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) allocated = .stop stop after) :
    evalValue (fuel + 2) config sourceFrame.interpretation.environment (.bytes (.varr (.int .u8)) bytes origin) before =
        .stop stop after ∧
      AcceptedWorld config sourceFrame.initialized after ambient types live (freshReceivingRegion before id :: regions) pending ∧
      AcceptedFrame config accepted sourceFrame after types := by
  have freshId := newDestination_fresh_id config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) before allocated id created
  subst id
  obtain ⟨frame⟩ := newDestination_fresh_frame config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) before allocated before.construction.destinations.size world.ownership.source.structural.1.1.1 created
  obtain ⟨ready⟩ := newDestination_initial_backing config.layout sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) before allocated before.construction.destinations.size (.int .u8) rfl created
  obtain ⟨row, present, packed, request, direct, receiver⟩ := newDestination_byteOwner_packed_value config.layout
    sourceFrame.interpretation.environment.act origin (some bytes.length) before allocated before.construction.destinations.size created
  have framePresent : allocated.construction.destinations[before.construction.destinations.size]? = some frame.row := by
    rw [frame.destinations]
    exact Array.getElem?_push_size
  have same : row = frame.row := Option.some.inj (present.symm.trans framePresent)
  subst row
  have readySame : ready.destination = frame.row := Option.some.inj (ready.present.symm.trans framePresent)
  have opened : frame.row.progress = .open 0 := by rw [← readySame]; exact ready.opened
  have allocatedWorld := newDestination_acceptedWorld config sourceFrame.interpretation.environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) sourceFrame.initialized before allocated before.construction.destinations.size ambient types live regions pending world created
  have current := newDestination_current_self config sourceFrame.initialized sourceFrame.interpretation.environment.act (.varr (.int .u8))
    .value origin (some bytes.length) before allocated before.construction.destinations.size ambient types live regions pending world created
  have preserved := bytes_writeLoop_stopped_world bytes origin config accepted sourceFrame before allocated after frame 0 direct opened
    ambient types live regions pending world source allocatedWorld.ownership.source current stop stopped
  have renewal : renewReceivingDestination before.construction.destinations.size allocated.construction =
      .ok before.construction.destinations.size allocated.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure, lookupDestination_result, framePresent, opened]
  have built : buildExpr (fuel + 1) config sourceFrame.interpretation.environment before.construction.destinations.size
      (.bytes (.varr (.int .u8)) bytes origin) allocated = .stop stop after := by
    have stopped' := stopped
    simp only [bind] at stopped'
    simp only [buildExpr, liftConstruction, renewal, bind, protectDestination]
    rw [stopped']
  refine ⟨?_, preserved⟩
  have created' := created
  simp only [EvalConfig.layout] at created'
  simp only [evalValue, Ty.nonfixed, constructLocal, producerCount?, literalCount, bind, ↓reduceIte, created', built]

#print axioms bytes_writeLoop_stopped_invariants
#print axioms FreshDestinationFrame.freshProtection
#print axioms bytes_writeLoop_stopped_world
#print axioms evalValue_byteOwner_writeStop_world

end Goose.Proofs.ConstructionAcceptedExecution
