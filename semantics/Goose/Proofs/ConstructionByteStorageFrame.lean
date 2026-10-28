import Goose.Proofs.ConstructionByteAllocationStopped

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ExitExecution

def reserveByteStorage (state : ExecutionState) : ExecutionState :=
  { state with construction := { state.construction with storage := state.construction.storage.push ⟨ByteArray.empty, 0⟩ } }

theorem reserveByteStorage_source (state : ExecutionState) (valid : OwnershipSourceState state.construction) :
    OwnershipSourceState (reserveByteStorage state).construction := by
  have preserved := constructionPrimitive_sourceState_of_sourceExtension (reserveStorage ByteArray.empty 0)
    (.reserveStorage ByteArray.empty 0) state.construction valid
    (reserveStorage_ownership_source ByteArray.empty 0 state.construction)
  simpa only [reserveByteStorage, reserveStorage, ConstructionM.get, ConstructionM.set, bind, pure,
    ConstructionResult.finalState] using preserved

theorem reserveByteStorage_observation (state : ExecutionState) (id : Nat) (storage : ReceivingStorage)
    (present : state.construction.storage[id]? = some storage) :
    AllocationObservation state (reserveByteStorage state) id := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  simp only [AllocationObservation, reserveByteStorage, Array.extract_size, Array.getElem?_push,
    Nat.ne_of_lt inside, ↓reduceIte, true_and]

theorem reserveByteStorage_stored_backing (state : ExecutionState) (layout : LayoutEnv) (stored : StoredValue)
    (backed : StoredValueBacking layout state stored) : StoredValueBacking layout (reserveByteStorage state) stored := by
  obtain ⟨storage, run, present, sampled, interval⟩ := backed.sampled layout state stored
  exact backed.allocation_frame layout state (reserveByteStorage state) stored
    (reserveByteStorage_observation state stored.storage storage present)

theorem reserveByteStorage_value_backing (state : ExecutionState) (layout : LayoutEnv) (value : Value)
    (backed : ValueStorageBacked layout state value) : ValueStorageBacked layout (reserveByteStorage state) value := by
  induction backed with
  | integer ty value => exact .integer ty value
  | boolean value => exact .boolean value
  | unit => exact .unit
  | reference location => exact .reference location
  | slice location start count => exact .slice location start count
  | array values children ih => exact .array values ih
  | record id values children ih => exact .record id values ih
  | stored stored backing => exact .stored stored (reserveByteStorage_stored_backing state layout stored backing)

theorem reserveByteStorage_observed (state : ExecutionState) (layout : LayoutEnv) (limit : Nat → Nat)
    (stored : StoredValue)
    (observed : StoredBackingObservation layout state limit stored) :
    StoredBackingObservation layout (reserveByteStorage state) limit stored := by
  obtain ⟨storage, run, fuel, finish, present, sampled, measured, lower, upper⟩ := observed.observed
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have next : (reserveByteStorage state).construction.storage[stored.storage]? = some storage := by
    simpa only [reserveByteStorage, Array.getElem?_push, Nat.ne_of_lt inside, ↓reduceIte] using present
  have sampledAfter := sampledStored_storage_transport stored state (reserveByteStorage state) storage storage run present next rfl
    (fun id named => rfl) sampled
  exact ⟨storage, run, fuel, finish, next, sampledAfter, measured, lower, upper⟩

theorem reserveByteStorage_rooted_backing (state : ExecutionState) (layout : LayoutEnv)
    (live : Goose.Core.RootInst → Prop) (valid : RootedBackingState layout state live) :
    RootedBackingState layout (reserveByteStorage state) live := by
  refine ⟨?_, valid.identities⟩
  intro root kept value found
  exact reserveByteStorage_value_backing state layout value (valid.values root kept value found)

theorem reserveByteStorage_protection (state : ExecutionState) (layout : LayoutEnv)
    (live : Goose.Core.RootInst → Prop) (region : ReceivingRegion)
    (valid : ReceivingProtection layout state live region) :
    ReceivingProtection layout (reserveByteStorage state) live region := by
  refine ⟨valid.present, ⟨⟨?_, ?_⟩, ?_⟩, valid.cutoff, valid.landing, valid.authority, valid.authorityBound, valid.names⟩
  · intro root kept value found
    exact reserveByteStorage_value_backing state layout value (valid.observations.backing.values root kept value found)
  · exact valid.observations.backing.identities
  · intro root kept value found stored occurrence
    exact reserveByteStorage_observed state layout region.limit stored
      (valid.observations.observations root kept value found stored occurrence)

theorem reserveByteStorage_stored_query (state : ExecutionState) (id : Nat) (row : PendingDestination)
    (stored : StoredValue) (present : state.construction.destinations[id]? = some row)
    (sampled : storedDestination id state = .ok stored state) :
    storedDestination id (reserveByteStorage state) = .ok stored (reserveByteStorage state) := by
  simp only [storedDestination, getDestination, EvalM.get, present, bind, pure, reserveByteStorage] at sampled ⊢
  cases count : progressCount row.progress with
  | none => simp only [count, fault, EvalM.stop] at sampled; cases sampled
  | some count =>
    simp only [count] at sampled ⊢
    cases sampled
    rfl

theorem reserveByteStorage_carrier_backing (state : ExecutionState) (layout : LayoutEnv) (carrier : Carrier)
    (valid : CarrierResultBacking layout state carrier) :
    CarrierResultBacking layout (reserveByteStorage state) carrier := by
  cases valid with
  | register value backed => exact .register value (reserveByteStorage_value_backing state layout value backed)
  | completed id count row stored present built sampled backed =>
    refine .completed id count row stored present built ?_ (reserveByteStorage_stored_backing state layout stored backed)
    exact reserveByteStorage_stored_query state _ _ stored present sampled
  | pendingNamed token incoming selected count snapshot source stored ticket present marked phase sampled backed =>
    refine .pendingNamed token incoming selected count snapshot source stored ticket present marked phase ?_
      (reserveByteStorage_stored_backing state layout stored backed)
    exact reserveByteStorage_stored_query state _ _ stored present sampled

#print axioms reserveByteStorage_carrier_backing
#print axioms reserveByteStorage_rooted_backing
#print axioms reserveByteStorage_protection
#print axioms reserveByteStorage_value_backing
#print axioms reserveByteStorage_observed
#print axioms reserveByteStorage_source
#print axioms reserveByteStorage_observation
end Goose.Proofs.ConstructionAcceptedExecution
