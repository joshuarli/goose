import Goose.Proofs.ConstructionAcceptedState
import Goose.Proofs.ConstructionRootedBackingAllocation
import Goose.Proofs.ExitExecutionReceiverReadiness

set_option Elab.async false

namespace Goose.Proofs.ConstructionRepresentation
open Goose.Construct

def storageExtent (state : ExecutionState) (id : Nat) : Nat :=
  ((state.construction.storage[id]?).map (fun storage => storage.bytes.size)).getD 0

theorem StoredValueBacking.named_bound (layout : LayoutEnv) (state : ExecutionState)
    (stored : StoredValue) (backed : StoredValueBacking layout state stored)
    (id : Nat) (named : stored.destination = some id) :
    id < state.construction.destinations.size := by
  cases backed with
  | detached storage element present detached type interval =>
      simp only [detached, reduceCtorEq] at named
  | named chosen storage destination count present marked binding backing type start progress element elementType interval =>
      have same : chosen = id := Option.some.inj (marked.symm.trans named)
      subst id
      exact (Array.getElem?_eq_some_iff.mp binding).1

theorem StoredValueBacking.newDestination_observation (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (knownCount : Option Nat) (before after : ExecutionState) (id : Nat) (stored : StoredValue)
    (backed : StoredValueBacking layout before stored)
    (executed : newDestination layout owner ty request origin none knownCount before = .ok id after) :
    StoredBackingObservation layout after (storageExtent before) stored := by
  obtain ⟨original, _, originalPresent, _, _⟩ :=
    backed.sampled layout before stored
  have frame : AllocationObservation before after stored.storage := by
    simpa only [executed, Goose.Proofs.Exit.stepState] using
      newDestination_existing_source layout owner ty request origin knownCount before stored.storage original originalPresent
  have next := backed.allocation_frame layout before after stored frame
  obtain ⟨current, run, present, sampled, interval⟩ := next.sampled layout after stored
  have same : current = original := Option.some.inj (present.symm.trans (frame.2.2.2.trans originalPresent))
  subst current
  obtain ⟨fuel, finish, measured, lower, upper⟩ := interval.interval
  exact ⟨original, run, fuel, finish, present, sampled, measured, lower,
    by simpa only [storageExtent, originalPresent, Option.map_some, Option.getD_some] using upper⟩

end Goose.Proofs.ConstructionRepresentation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionRepresentation

theorem newDestination_fresh_id (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (knownCount : Option Nat) (before after : ExecutionState) (id : Nat)
    (executed : newDestination layout owner ty request origin none knownCount before = .ok id after) :
    id = before.construction.destinations.size := by
  let prepared : ExecutionState := { before with construction :=
    { before.construction with storage := before.construction.storage.push ⟨ByteArray.empty, 0⟩ } }
  have query := Goose.Proofs.ConstructionExecutionProtocol.stateQuery_receivingLayout layout ty prepared
  simp only [newDestination, liftConstruction, reserveStorage, ConstructionM.get,
    ConstructionM.set, bind, pure] at executed
  change ((receivingLayout layout ty >>= fun selected => liftConstruction origin
    (openDestination before.construction.storage.size
      ⟨0, ⟨.local owner 0 0, []⟩, ty, ty, request, 0, owner⟩ selected knownCount)) prepared) = .ok id after at executed
  cases result : receivingLayout layout ty prepared with
  | ok selected middle =>
      simp only [result, Goose.Proofs.Exit.stepState] at query
      subst middle
      simp only [bind, result, liftConstruction] at executed
      cases opened : openDestination before.construction.storage.size
          ⟨0, ⟨.local owner 0 0, []⟩, ty, ty, request, 0, owner⟩ selected knownCount prepared.construction with
      | fault reason final => simp only [opened] at executed; cases executed
      | ok value final =>
          simp only [opened] at executed
          cases executed
          exact (Goose.Proofs.ExitExecution.openDestination_receiver_row prepared.construction final _ _ _ _ id opened).1
  | stop reason middle | escape target carriers middle | jump target kind middle =>
      simp only [bind, result] at executed
      cases executed

def freshReceivingRegion (before : ExecutionState) (id : Nat) : ReceivingRegion :=
  ⟨id, fun _ => False, storageExtent before, [id]⟩

theorem newDestination_receivingProtection (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (knownCount : Option Nat) (before after : ExecutionState) (id : Nat)
    (liveRoots : RootInst → Prop) (backed : RootedBackingState layout before liveRoots)
    (executed : newDestination layout owner ty request origin none knownCount before = .ok id after) :
    ReceivingProtection layout after liveRoots (freshReceivingRegion before id) := by
  obtain ⟨destination, present, receiver, fresh⟩ :=
    newDestination_success_fresh layout owner ty request origin knownCount before after id executed
  have objects : after.objects = before.objects := by
    simpa only [executed, Goose.Proofs.Exit.stepState] using
      (newDestination_objects layout owner ty request origin knownCount before).1
  have nextBacking : RootedBackingState layout after liveRoots := by
    simpa only [executed, Goose.Proofs.Exit.stepState] using
      backed.newDestination_frame layout owner ty request origin knownCount before liveRoots
  have extent : storageExtent before destination.storage = 0 := by
    simp only [storageExtent, Array.getElem?_eq_none_iff.mpr fresh, Option.map_none, Option.getD_none]
  refine ⟨⟨destination, present⟩, ⟨?_, ?_⟩, ?_, ?_, by simp [freshReceivingRegion], ?_⟩
  · exact ⟨fun root retained value found => nextBacking.values root retained.1 value found,
      fun root retained stored found => nextBacking.identities root retained.1 stored found⟩
  · intro root retained value found stored occurrence
    have oldFound : before.objects.lookup root = some value := by rw [objects] at found; exact found
    exact ((backed.values root retained.1 value oldFound).occurrence_backing layout before value stored occurrence).newDestination_observation
      layout owner ty request origin knownCount before after id stored executed
  · intro row found
    have same : row = destination := Option.some.inj (found.symm.trans present)
    subst row
    simpa only [freshReceivingRegion, extent] using Nat.zero_le destination.rollbackEnd
  · intro row found
    have same : row = destination := Option.some.inj (found.symm.trans present)
    subst row
    simpa only [freshReceivingRegion, extent] using Nat.zero_le destination.capability.start
  · intro root retained outside value found stored occurrence namedId named
    have oldFound : before.objects.lookup root = some value := by rw [objects] at found; exact found
    have bound := ((backed.values root retained value oldFound).occurrence_backing layout before value stored occurrence).named_bound
      layout before stored namedId named
    have allocated := newDestination_fresh_id layout owner ty request origin knownCount before after id executed
    change namedId ∉ [id]
    simp only [List.mem_singleton]
    intro equal
    exact (Nat.ne_of_lt bound) (equal.trans allocated)

#print axioms newDestination_fresh_id
#print axioms newDestination_receivingProtection

end Goose.Proofs.ConstructionAcceptedExecution
