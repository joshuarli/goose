import Goose.Proofs.ConstructionByteStorageFrame
import Goose.Proofs.ExitExecutionLiveCarriers

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ExitExecution

private theorem reserveByteStorage_currentSteps (state : ExecutionState) (fuel id : Nat) :
    destinationCurrentSteps fuel (reserveByteStorage state).construction id =
      destinationCurrentSteps fuel state.construction id := by
  induction fuel generalizing id with
  | zero => rfl
  | succ fuel ih =>
    simp only [destinationCurrentSteps,
      show (reserveByteStorage state).construction.destinations = state.construction.destinations from rfl,
      show (reserveByteStorage state).construction.destinationSuccessors = state.construction.destinationSuccessors from rfl]
    split <;> simp_all

private theorem reserveByteStorage_current (state : ExecutionState) (id : Nat) :
    destinationCurrent (reserveByteStorage state).construction id = destinationCurrent state.construction id := by
  simp only [destinationCurrent, reserveByteStorage]
  exact reserveByteStorage_currentSteps state _ id

private theorem reserveByteStorage_parent (state : ExecutionState) (id : Nat) (row : PendingDestination)
    (ready : LandingParentReady state.construction id row) :
    LandingParentReady (reserveByteStorage state).construction id row := by
  cases ready with
  | receiver use => exact .receiver use
  | child parent count owner use present progress => exact .child parent count owner use present progress
  | replacement parent count owner use present progress => exact .replacement parent count owner use present progress

private def reserveByteStorage_receiving (state : ExecutionState) (incoming source : Nat)
    (ready : ReceivingCarrierLandingReady state incoming source) :
    ReceivingCarrierLandingReady (reserveByteStorage state) incoming source := by
  exact ⟨ready.receiving, ready.sourceDestination, ready.receivingDestination,
    (reserveByteStorage_current state incoming).trans ready.resolved, ready.sourcePresent, ready.receivingPresent,
    ready.path, reserveByteStorage_parent state ready.receiving ready.receivingDestination ready.parent, ready.ordered⟩

theorem reserveByteStorage_carrier_ready (state : ExecutionState) (channel : Channel) (carrier : Carrier)
    (ready : CarrierLandingReady state channel carrier) :
    CarrierLandingReady (reserveByteStorage state) channel carrier := by
  cases ready with
  | register ty value => exact .register ty value
  | construct incoming source ready => exact .construct incoming source (reserveByteStorage_receiving state incoming source ready)
  | completion token incoming selected source role snapshot ticket ready =>
    exact .completion token incoming selected source role snapshot ticket (reserveByteStorage_receiving state selected source ready)
  | pendingNamed token incoming selected snapshot ticket => exact .pendingNamed token incoming selected snapshot ticket

theorem reserveByteStorage_carriers_ready (state : ExecutionState) (channels : List Channel) (carriers : List Carrier)
    (ready : CarriersLandingReady state channels carriers) :
    CarriersLandingReady (reserveByteStorage state) channels carriers :=
  ⟨ready.lengths, fun channel carrier member => reserveByteStorage_carrier_ready state channel carrier (ready.pairs channel carrier member)⟩

#print axioms reserveByteStorage_carrier_ready
#print axioms reserveByteStorage_carriers_ready

end Goose.Proofs.ConstructionAcceptedExecution
