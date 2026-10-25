import Goose.Proofs.ConstructionRootedBacking
import Goose.Proofs.ExitExecutionStoredPrefixReads

set_option Elab.async false

namespace Goose.Proofs.ConstructionRepresentation
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ExitExecution (BytePrefixEqual)

inductive StoredOccurrence : Value → StoredValue → Prop
  | stored (value : StoredValue) : StoredOccurrence (.stored value) value
  | array (values : Array Value) (value : Value) (stored : StoredValue)
      (member : value ∈ values.toList) (child : StoredOccurrence value stored) :
      StoredOccurrence (.fixed values) stored
  | record (id : Nat) (values : Array Value) (value : Value) (stored : StoredValue)
      (member : value ∈ values.toList) (child : StoredOccurrence value stored) :
      StoredOccurrence (.record id values) stored

structure StoredBackingObservation (layout : LayoutEnv) (state : ExecutionState)
    (limit : Nat → Nat) (stored : StoredValue) : Prop where
  observed : ∃ storage run fuel finish,
    state.construction.storage[stored.storage]? = some storage ∧
    sampledStored stored state = .ok (storage.bytes, run) state ∧
    elementsEnd fuel layout run.element (storedWrittenRun stored run).count
      storage.bytes run.byteStart = .ok finish ∧
    run.byteStart ≤ finish ∧ finish ≤ limit stored.storage

structure StoredBackingPrefixFrame (before after : ExecutionState) (limit : Nat → Nat)
    (stored : StoredValue) : Prop where
  storage : ∃ original current,
    before.construction.storage[stored.storage]? = some original ∧
    after.construction.storage[stored.storage]? = some current ∧
    BytePrefixEqual original.bytes current.bytes (limit stored.storage) ∧
    current.publishedCount = original.publishedCount
  destination : ∀ id, stored.destination = some id →
    after.construction.destinations[id]? = before.construction.destinations[id]?

structure RootedBackingObservations (layout : LayoutEnv) (state : ExecutionState)
    (retainedRoot : RootInst → Prop) (limit : Nat → Nat) : Prop where
  backing : RootedBackingState layout state retainedRoot
  observations : ∀ root, retainedRoot root → ∀ value,
    state.objects.lookup root = some value → ∀ stored, StoredOccurrence value stored →
    StoredBackingObservation layout state limit stored

structure RootedBackingPrefixFrame (before after : ExecutionState)
    (retainedRoot : RootInst → Prop) (limit : Nat → Nat) : Prop where
  objects : ∀ root, retainedRoot root → after.objects.lookup root = before.objects.lookup root
  identities : ∀ root, retainedRoot root →
    after.objectOrdinals.lookup root = before.objectOrdinals.lookup root
  sources : ∀ root, retainedRoot root → ∀ value,
    before.objects.lookup root = some value → ∀ stored, StoredOccurrence value stored →
    StoredBackingPrefixFrame before after limit stored

theorem initial_rootedBackingObservations (layout : LayoutEnv) (retainedRoot : RootInst → Prop)
    (limit : Nat → Nat) : RootedBackingObservations layout .initial retainedRoot limit := by
  refine ⟨initial_rootedBackingState layout retainedRoot, ?_⟩
  intro root retained value present
  cases present

theorem StoredValueBacking.observation (layout : LayoutEnv) (state : ExecutionState)
    (stored : StoredValue) (backed : StoredValueBacking layout state stored) :
    StoredBackingObservation layout state
      (fun id => ((state.construction.storage[id]?).map (fun storage => storage.bytes.size)).getD 0) stored := by
  obtain ⟨storage, run, present, sampled, interval⟩ := backed.sampled layout state stored
  obtain ⟨fuel, finish, measured, lower, upper⟩ := interval.interval
  refine ⟨storage, run, fuel, finish, present, sampled, ?_, lower, ?_⟩
  · exact measured
  · simpa only [present, Option.map_some, Option.getD_some] using upper

theorem ValueStorageBacked.occurrence_backing (layout : LayoutEnv) (state : ExecutionState)
    (value : Value) (backed : ValueStorageBacked layout state value)
    (stored : StoredValue) (occurrence : StoredOccurrence value stored) :
    StoredValueBacking layout state stored := by
  induction occurrence with
  | stored value => cases backed with | stored _ backing => exact backing
  | array values value stored member child ih =>
      cases backed with | array _ children => exact ih (children value member)
  | record id values value stored member child ih =>
      cases backed with | record _ _ children => exact ih (children value member)

theorem RootedBackingState.observations (layout : LayoutEnv) (state : ExecutionState)
    (retainedRoot : RootInst → Prop) (valid : RootedBackingState layout state retainedRoot) :
    RootedBackingObservations layout state retainedRoot
      (fun id => ((state.construction.storage[id]?).map (fun storage => storage.bytes.size)).getD 0) := by
  refine ⟨valid, ?_⟩
  intro root retained value present stored occurrence
  exact ((valid.values root retained value present).occurrence_backing layout state value stored occurrence).observation
    layout state stored

theorem StoredBackingObservation.prefix_frame (layout : LayoutEnv) (before after : ExecutionState)
    (limit : Nat → Nat) (stored : StoredValue)
    (observation : StoredBackingObservation layout before limit stored)
    (frame : StoredBackingPrefixFrame before after limit stored) :
    StoredBackingObservation layout after limit stored := by
  obtain ⟨storage, run, fuel, finish, present, sampled, measured, lower, upper⟩ := observation.observed
  obtain ⟨original, current, originalFound, currentFound, bytes, published⟩ := frame.storage
  have same := Option.some.inj (originalFound.symm.trans present)
  subst original
  refine ⟨current, run, fuel, finish, currentFound,
    Goose.Proofs.ExitExecution.sampledStored_storage_transport stored before after storage current run
      present currentFound published frame.destination sampled, bytes.elementsEnd fuel layout run.element
        (storedWrittenRun stored run).count run.byteStart finish measured upper, lower, upper⟩

theorem StoredValueBacking.prefix_frame (layout : LayoutEnv) (before after : ExecutionState)
    (limit : Nat → Nat) (stored : StoredValue)
    (backed : StoredValueBacking layout before stored)
    (observation : StoredBackingObservation layout before limit stored)
    (frame : StoredBackingPrefixFrame before after limit stored) :
    StoredValueBacking layout after stored := by
  have next := observation.prefix_frame layout before after limit stored frame
  obtain ⟨observedStorage, run, fuel, finish, observedFound, sampled, measured, lower, upper⟩ := next.observed
  obtain ⟨original, current, originalFound, currentFound, bytes, published⟩ := frame.storage
  have same := Option.some.inj (observedFound.symm.trans currentFound)
  subst observedStorage
  have interval : SampledRunBacking layout current.bytes (storedWrittenRun stored run) :=
    ⟨fuel, finish, measured, lower, Nat.le_trans upper bytes.afterBound⟩
  cases backed with
  | detached storage element present detached type bounded =>
      simp only [sampledStored, getStorage, EvalM.get, bind, currentFound, pure,
        detached, type, ExecutionStep.ok.injEq, Prod.mk.injEq, true_and, and_true] at sampled
      cases sampled
      exact .detached current element currentFound detached type interval
  | named id storage destination count present named binding backing type start progress element elementType bounded =>
      have rows := (frame.destination id named).trans binding
      have runSame : run = ⟨stored.start + (if destination.layout == .packed &&
          destination.capability.request == .value then 4 else 0),
          (match destination.progress with | .published _ => current.publishedCount | _ => count), element⟩ := by
        cases currentProgress : destination.progress <;>
          simp_all only [progressCount, Option.some.injEq, sampledStored, getStorage, getDestination,
            EvalM.get, bind, pure, Goose.Construct.fault, EvalM.stop, ExecutionStep.ok.injEq,
            Prod.mk.injEq, true_and, and_true, reduceCtorEq]
      subst run
      exact .named id current destination count currentFound named rows backing type start progress
        element elementType interval

theorem ValueStorageBacked.prefix_frame (layout : LayoutEnv) (before after : ExecutionState)
    (limit : Nat → Nat) (value : Value) (backed : ValueStorageBacked layout before value)
    (observed : ∀ stored, StoredOccurrence value stored → StoredBackingObservation layout before limit stored)
    (frames : ∀ stored, StoredOccurrence value stored → StoredBackingPrefixFrame before after limit stored) :
    ValueStorageBacked layout after value := by
  induction backed with
  | integer ty value => exact .integer ty value
  | boolean value => exact .boolean value
  | unit => exact .unit
  | reference location => exact .reference location
  | slice location start count => exact .slice location start count
  | array values children ih =>
      exact .array values (fun value member => ih value member
        (fun stored occurrence => observed stored (.array values value stored member occurrence))
        (fun stored occurrence => frames stored (.array values value stored member occurrence)))
  | record id values children ih =>
      exact .record id values (fun value member => ih value member
        (fun stored occurrence => observed stored (.record id values value stored member occurrence))
        (fun stored occurrence => frames stored (.record id values value stored member occurrence)))
  | stored stored backing =>
      exact .stored stored (backing.prefix_frame layout before after limit stored
        (observed stored (.stored stored)) (frames stored (.stored stored)))

theorem RootedBackingObservations.prefix_frame (layout : LayoutEnv) (before after : ExecutionState)
    (retainedRoot : RootInst → Prop) (limit : Nat → Nat)
    (valid : RootedBackingObservations layout before retainedRoot limit)
    (frame : RootedBackingPrefixFrame before after retainedRoot limit) :
    RootedBackingObservations layout after retainedRoot limit := by
  constructor
  · constructor
    · intro root retained value present
      rw [frame.objects root retained] at present
      exact (valid.backing.values root retained value present).prefix_frame layout before after limit value
        (valid.observations root retained value present) (frame.sources root retained value present)
    · intro root retained stored present
      rw [frame.objects root retained] at present
      rw [frame.identities root retained]
      exact valid.backing.identities root retained stored present
  · intro root retained value present stored occurrence
    rw [frame.objects root retained] at present
    exact (valid.observations root retained value present stored occurrence).prefix_frame
      layout before after limit stored (frame.sources root retained value present stored occurrence)

#print axioms initial_rootedBackingObservations
#print axioms StoredValueBacking.observation
#print axioms ValueStorageBacked.occurrence_backing
#print axioms RootedBackingState.observations
#print axioms StoredBackingObservation.prefix_frame
#print axioms StoredValueBacking.prefix_frame
#print axioms ValueStorageBacked.prefix_frame
#print axioms RootedBackingObservations.prefix_frame

end Goose.Proofs.ConstructionRepresentation
