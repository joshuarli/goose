import Goose.Proofs.ConstructionByteStorageCarriers

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ExitExecution

def appendStdoutState (bytes : ByteArray) (state : ExecutionState) : ExecutionState :=
  { state with construction := { state.construction with stdout := state.construction.stdout ++ bytes } }

theorem appendStdout_observation (bytes : ByteArray) (state : ExecutionState) (id : Nat) (storage : ReceivingStorage)
    (present : state.construction.storage[id]? = some storage) :
    AllocationObservation state (appendStdoutState bytes state) id := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  simp only [AllocationObservation, appendStdoutState, Array.extract_size, Array.getElem?_push,
    Nat.ne_of_lt inside, ↓reduceIte, true_and]

theorem appendStdout_stored_backing (bytes : ByteArray) (state : ExecutionState) (layout : LayoutEnv) (stored : StoredValue)
    (backed : StoredValueBacking layout state stored) : StoredValueBacking layout (appendStdoutState bytes state) stored := by
  obtain ⟨storage, run, present, sampled, interval⟩ := backed.sampled layout state stored
  exact backed.allocation_frame layout state (appendStdoutState bytes state) stored
    (appendStdout_observation bytes state stored.storage storage present)

theorem appendStdout_value_backing (bytes : ByteArray) (state : ExecutionState) (layout : LayoutEnv) (value : Value)
    (backed : ValueStorageBacked layout state value) : ValueStorageBacked layout (appendStdoutState bytes state) value := by
  induction backed with
  | integer ty value => exact .integer ty value
  | boolean value => exact .boolean value
  | unit => exact .unit
  | reference location => exact .reference location
  | slice location start count => exact .slice location start count
  | array values children ih => exact .array values ih
  | record id values children ih => exact .record id values ih
  | stored stored backing => exact .stored stored (appendStdout_stored_backing bytes state layout stored backing)

theorem appendStdout_observed (bytes : ByteArray) (state : ExecutionState) (layout : LayoutEnv) (limit : Nat → Nat)
    (stored : StoredValue)
    (observed : StoredBackingObservation layout state limit stored) :
    StoredBackingObservation layout (appendStdoutState bytes state) limit stored := by
  obtain ⟨storage, run, fuel, finish, present, sampled, measured, lower, upper⟩ := observed.observed
  have next : (appendStdoutState bytes state).construction.storage[stored.storage]? = some storage := present
  have sampledAfter := sampledStored_storage_transport stored state (appendStdoutState bytes state) storage storage run present next rfl
    (fun id named => rfl) sampled
  exact ⟨storage, run, fuel, finish, next, sampledAfter, measured, lower, upper⟩

theorem appendStdout_rooted_backing (bytes : ByteArray) (state : ExecutionState) (layout : LayoutEnv)
    (live : Goose.Core.RootInst → Prop) (valid : RootedBackingState layout state live) :
    RootedBackingState layout (appendStdoutState bytes state) live := by
  refine ⟨?_, valid.identities⟩
  intro root kept value found
  exact appendStdout_value_backing bytes state layout value (valid.values root kept value found)

theorem appendStdout_protection (bytes : ByteArray) (state : ExecutionState) (layout : LayoutEnv)
    (live : Goose.Core.RootInst → Prop) (region : ReceivingRegion)
    (valid : ReceivingProtection layout state live region) :
    ReceivingProtection layout (appendStdoutState bytes state) live region := by
  refine ⟨valid.present, ⟨⟨?_, ?_⟩, ?_⟩, valid.cutoff, valid.landing, valid.authority, valid.authorityBound, valid.names⟩
  · intro root kept value found
    exact appendStdout_value_backing bytes state layout value (valid.observations.backing.values root kept value found)
  · exact valid.observations.backing.identities
  · intro root kept value found stored occurrence
    exact appendStdout_observed bytes state layout region.limit stored
      (valid.observations.observations root kept value found stored occurrence)

theorem appendStdout_stored_query (bytes : ByteArray) (state : ExecutionState) (id : Nat) (row : PendingDestination)
    (stored : StoredValue) (present : state.construction.destinations[id]? = some row)
    (sampled : storedDestination id state = .ok stored state) :
    storedDestination id (appendStdoutState bytes state) = .ok stored (appendStdoutState bytes state) := by
  simp only [storedDestination, getDestination, EvalM.get, present, bind, pure, appendStdoutState] at sampled ⊢
  cases count : progressCount row.progress with
  | none => simp only [count, fault, EvalM.stop] at sampled; cases sampled
  | some count =>
    simp only [count] at sampled ⊢
    cases sampled
    rfl

theorem appendStdout_carrier_backing (bytes : ByteArray) (state : ExecutionState) (layout : LayoutEnv) (carrier : Carrier)
    (valid : CarrierResultBacking layout state carrier) :
    CarrierResultBacking layout (appendStdoutState bytes state) carrier := by
  cases valid with
  | register value backed => exact .register value (appendStdout_value_backing bytes state layout value backed)
  | completed id count row stored present built sampled backed =>
    refine .completed id count row stored present built ?_ (appendStdout_stored_backing bytes state layout stored backed)
    exact appendStdout_stored_query bytes state _ _ stored present sampled
  | pendingNamed token incoming selected count snapshot source stored ticket present marked phase sampled backed =>
    refine .pendingNamed token incoming selected count snapshot source stored ticket present marked phase ?_
      (appendStdout_stored_backing bytes state layout stored backed)
    exact appendStdout_stored_query bytes state _ _ stored present sampled

private theorem appendStdout_currentSteps (bytes : ByteArray) (state : ExecutionState) (fuel id : Nat) :
    destinationCurrentSteps fuel (appendStdoutState bytes state).construction id =
      destinationCurrentSteps fuel state.construction id := by
  induction fuel generalizing id with
  | zero => rfl
  | succ fuel ih =>
    simp only [destinationCurrentSteps,
      show (appendStdoutState bytes state).construction.destinations = state.construction.destinations from rfl,
      show (appendStdoutState bytes state).construction.destinationSuccessors = state.construction.destinationSuccessors from rfl]
    split <;> simp_all

private theorem appendStdout_current (bytes : ByteArray) (state : ExecutionState) (id : Nat) :
    destinationCurrent (appendStdoutState bytes state).construction id = destinationCurrent state.construction id := by
  simp only [destinationCurrent, appendStdoutState]
  exact appendStdout_currentSteps bytes state _ id

private theorem appendStdout_parent (bytes : ByteArray) (state : ExecutionState) (id : Nat) (row : PendingDestination)
    (ready : LandingParentReady state.construction id row) :
    LandingParentReady (appendStdoutState bytes state).construction id row := by
  cases ready with
  | receiver use => exact .receiver use
  | child parent count owner use present progress => exact .child parent count owner use present progress
  | replacement parent count owner use present progress => exact .replacement parent count owner use present progress

private def appendStdout_receiving (bytes : ByteArray) (state : ExecutionState) (incoming source : Nat)
    (ready : ReceivingCarrierLandingReady state incoming source) :
    ReceivingCarrierLandingReady (appendStdoutState bytes state) incoming source := by
  exact ⟨ready.receiving, ready.sourceDestination, ready.receivingDestination,
    (appendStdout_current bytes state incoming).trans ready.resolved, ready.sourcePresent, ready.receivingPresent,
    ready.path, appendStdout_parent bytes state ready.receiving ready.receivingDestination ready.parent, ready.ordered⟩

theorem appendStdout_carrier_ready (bytes : ByteArray) (state : ExecutionState) (channel : Channel) (carrier : Carrier)
    (ready : CarrierLandingReady state channel carrier) :
    CarrierLandingReady (appendStdoutState bytes state) channel carrier := by
  cases ready with
  | register ty value => exact .register ty value
  | construct incoming source ready => exact .construct incoming source (appendStdout_receiving bytes state incoming source ready)
  | completion token incoming selected source role snapshot ticket ready =>
    exact .completion token incoming selected source role snapshot ticket (appendStdout_receiving bytes state selected source ready)
  | pendingNamed token incoming selected snapshot ticket => exact .pendingNamed token incoming selected snapshot ticket

theorem appendStdout_carriers_ready (bytes : ByteArray) (state : ExecutionState) (channels : List Channel) (carriers : List Carrier)
    (ready : CarriersLandingReady state channels carriers) :
    CarriersLandingReady (appendStdoutState bytes state) channels carriers :=
  ⟨ready.lengths, fun channel carrier member => appendStdout_carrier_ready bytes state channel carrier (ready.pairs channel carrier member)⟩

#print axioms appendStdout_carriers_ready
#print axioms appendStdout_carrier_backing
#print axioms appendStdout_protection
end Goose.Proofs.ConstructionAcceptedExecution
