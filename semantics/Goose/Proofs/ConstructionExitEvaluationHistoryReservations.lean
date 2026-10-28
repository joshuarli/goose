import Goose.Proofs.ConstructionExitEvaluationHistoryPrimitives
import Goose.Proofs.ConstructionExecutionProtocolReservationPrimitives
import Goose.Proofs.ExitExecutionOwnedReceiptSetup

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem evaluationHistoryLifecycle_reservation (origin : OriginId) (action : ConstructionM α)
    (primitive : ConstructionReservationPrimitive action) (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame)
    (size : ∀ state, ReservationLifecycleInvariant state →
      state.exitReservations.size ≤ (action state).finalState.exitReservations.size) :
    PreservesEvaluationHistoryLifecycle (liftConstruction origin action) ambient pending := by
  intro state valid
  have lifecycle := reservationLifecycleReservationPrimitives.preserves action primitive state.construction valid.1
  have bounded := reservationReferencesBounded_mono state.construction (action state.construction).finalState ambient
    (size state.construction valid.1) valid.2.1
  have coverage := valid.2.2
  cases result : action state.construction with
  | ok value construction =>
    simp only [result, ConstructionResult.finalState] at lifecycle bounded
    simpa only [liftConstruction, result, Goose.Proofs.Exit.stepState, EvaluationHistoryLifecycle,
      EvaluationHistoryCoverage] using And.intro lifecycle (And.intro bounded coverage)
  | fault kind construction =>
    simp only [result, ConstructionResult.finalState] at lifecycle bounded
    cases kind <;> simpa only [liftConstruction, result, Goose.Proofs.Exit.stepState, EvaluationHistoryLifecycle,
      EvaluationHistoryCoverage] using And.intro lifecycle (And.intro bounded coverage)

theorem evaluationHistoryLifecycle_wait (origin : OriginId) (id : Nat)
    (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame) :
    PreservesEvaluationHistoryLifecycle (liftConstruction origin (waitExitDestination id)) ambient pending := by
  apply evaluationHistoryLifecycle_reservation origin _ (.waitExitDestination id) ambient pending
  intro state valid
  simp [waitExitDestination, ConstructionM.get, ConstructionM.set, bind, pure, ConstructionResult.finalState]

theorem evaluationHistoryLifecycle_release (origin : OriginId) (token : Nat)
    (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame) :
    PreservesEvaluationHistoryLifecycle (liftConstruction origin (releaseExitReservation token)) ambient pending := by
  apply evaluationHistoryLifecycle_reservation origin _ (.releaseExitReservation token) ambient pending
  intro state valid
  simp only [releaseExitReservation, ConstructionM.get, bind]
  cases ticket : state.exitReservations[token]? with
  | none => simp [ticket, ConstructionM.fail, ConstructionResult.finalState]
  | some status =>
    cases status <;> simp [ticket, ConstructionM.set, ConstructionM.fail, pure, bind, ConstructionResult.finalState]

theorem evaluationHistoryLifecycle_land_chain (origin : OriginId) (id : Nat)
    (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame) :
    PreservesEvaluationHistoryLifecycle (liftConstruction origin (landExitReplacementChain id)) ambient pending := by
  apply evaluationHistoryLifecycle_reservation origin _ (.landExitReplacementChain id) ambient pending
  intro state valid
  have frame := landExitReplacementChain_reservation_frame id state valid.1
  rw [frame.tickets]
  exact Nat.le_refl _

theorem evaluationHistoryLifecycle_land_into (origin : OriginId) (receiving id : Nat)
    (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame) :
    PreservesEvaluationHistoryLifecycle (liftConstruction origin (landExitReplacementInto receiving id)) ambient pending := by
  apply evaluationHistoryLifecycle_reservation origin _ (.landExitReplacementInto receiving id) ambient pending
  intro state valid
  have frame := landExitReplacementInto_reservation_frame receiving id state valid.1
  rw [frame.tickets]
  exact Nat.le_refl _

theorem evaluationHistoryLifecycle_rearm (origin : OriginId) (borrowed : BorrowedWaitingExitReservation)
    (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame) :
    PreservesEvaluationHistoryLifecycle (liftConstruction origin (rearmExitReservation borrowed)) ambient pending := by
  apply evaluationHistoryLifecycle_reservation origin _ (.rearmExitReservation borrowed) ambient pending
  intro state valid
  by_cases restored : state.exitReservations[borrowed.token]? = some .restored
  · cases resolved : destinationCurrent state borrowed.incoming with
    | error reason =>
      simp [rearmExitReservation_unresolved state borrowed reason restored resolved, ConstructionResult.finalState]
    | ok current =>
      cases present : state.destinations[current]? with
      | none =>
        simp [rearmExitReservation_missing state borrowed current restored resolved present, ConstructionResult.finalState]
      | some row =>
        simp [rearmExitReservation_restored state borrowed current row restored resolved present, ConstructionResult.finalState]
  · simp [rearmExitReservation_not_restored state borrowed restored, ConstructionResult.finalState]

theorem evaluationHistoryLifecycle_reserve (origin : OriginId) (incoming : Nat) (source : ExitSource)
    (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame) :
    PreservesEvaluationHistoryLifecycle (liftConstruction origin (reserveExitDestination incoming source)) ambient pending := by
  apply evaluationHistoryLifecycle_reservation origin _ (.reserveExitDestination incoming source) ambient pending
  intro state valid
  have frame := Goose.Proofs.ExitExecution.prepareExitDestination_tickets incoming source state valid
  change state.exitReservations.size ≤ ((do
    let (current, snapshot) ← prepareExitDestinationAction incoming source
    let after ← ConstructionM.get
    let token := after.exitReservations.size
    ConstructionM.set { after with exitReservations := after.exitReservations.push (.active (if source == ExitSource.namedResult then .named .awaitingSource else .fresh) incoming current snapshot) }
    pure (token, current)) state).finalState.exitReservations.size
  simp only [bind]
  cases result : prepareExitDestinationAction incoming source state with
  | fault reason after =>
    simp only [result, ConstructionResult.finalState] at frame
    simp only [result, ConstructionResult.finalState, frame, Nat.le_refl]
  | ok pair after =>
    obtain ⟨current, snapshot⟩ := pair
    simp only [result, ConstructionResult.finalState] at frame
    simp only [result, ConstructionM.get, ConstructionM.set, bind, pure, ConstructionResult.finalState,
      Array.size_push, frame]
    omega

theorem evaluationHistoryLifecycle_select_waiting (origin : OriginId) (token : Nat) (source : ExitSource)
    (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame) :
    PreservesEvaluationHistoryLifecycle (liftConstruction origin (selectWaitingExitDestination token source)) ambient pending := by
  apply evaluationHistoryLifecycle_reservation origin _ (.selectWaitingExitDestination token source) ambient pending
  intro state valid
  simp only [selectWaitingExitDestination, ConstructionM.get, bind]
  cases ticket : state.exitReservations[token]? with
  | none => simp [ticket, ConstructionM.fail, ConstructionResult.finalState]
  | some status =>
    cases status with
    | waiting incoming =>
      have frame := Goose.Proofs.ExitExecution.prepareExitDestination_tickets incoming source state valid
      cases result : prepareExitDestinationAction incoming source state with
      | fault reason after =>
        simp only [result, ConstructionResult.finalState] at frame
        simpa only [ticket, result, bind, ConstructionResult.finalState, frame] using Nat.le_refl state.exitReservations.size
      | ok pair after =>
        obtain ⟨selected, snapshot⟩ := pair
        simp only [result, ConstructionResult.finalState] at frame
        simpa only [ticket, result, ConstructionM.get, ConstructionM.set, bind, pure, ConstructionResult.finalState,
          Array.size_set!, frame] using Nat.le_refl state.exitReservations.size
    | active role incoming selected snapshot => simp [ticket, ConstructionM.fail, ConstructionResult.finalState]
    | restored => simp [ticket, ConstructionM.fail, ConstructionResult.finalState]
    | released => simp [ticket, ConstructionM.fail, ConstructionResult.finalState]

theorem evaluationHistoryLifecycle_renew (origin : OriginId) (incoming : Nat)
    (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame) :
    PreservesEvaluationHistoryLifecycle (liftConstruction origin (renewReceivingDestination incoming)) ambient pending := by
  apply evaluationHistoryLifecycle_reservation origin _ (.renewReceivingDestination incoming) ambient pending
  intro state valid
  have frame := renewReceivingDestination_reservation_frame incoming state valid.1 valid.2.resumptions
  rw [frame.tickets]
  exact Nat.le_refl _

#print axioms evaluationHistoryLifecycle_renew
#print axioms evaluationHistoryLifecycle_select_waiting
#print axioms evaluationHistoryLifecycle_reserve
#print axioms evaluationHistoryLifecycle_land_chain
#print axioms evaluationHistoryLifecycle_land_into
#print axioms evaluationHistoryLifecycle_rearm
#print axioms evaluationHistoryLifecycle_reservation
#print axioms evaluationHistoryLifecycle_wait
#print axioms evaluationHistoryLifecycle_release

end Goose.Proofs.ConstructionAcceptedExecution
