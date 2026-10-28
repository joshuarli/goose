import Goose.Proofs.ConstructionExitEvaluationHistoryReservations

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem evaluationHistoryLifecycle_mark_named (origin : OriginId) (token : Nat)
    (ambient : OwnershipAmbient) (pending : List PendingCarrierFrame) :
    PreservesEvaluationHistoryLifecycle (liftConstruction origin (markNamedReservation token)) ambient pending := by
  apply evaluationHistoryLifecycle_reservation origin _ (.markNamedReservation token) ambient pending
  intro state valid
  simp only [markNamedReservation, ConstructionM.get, bind]
  cases ticket : state.exitReservations[token]? with
  | none => exact Nat.le_refl _
  | some reservation =>
    cases reservation with
    | waiting incoming | restored | released => exact Nat.le_refl _
    | active role incoming selected old =>
      cases role with
      | fresh => exact Nat.le_refl _
      | named stage =>
        cases stage with
        | ready | materialized => exact Nat.le_refl _
        | awaitingSource =>
          simp only [pure, lookupDestination_result, bind]
          cases present : state.destinations[selected]? with
          | none => exact Nat.le_refl _
          | some source =>
            simp only [present]
            cases progress : source.progress <;> simp only [progress] <;> try exact Nat.le_refl _
            case built count | suspended count nested | exiting count nested =>
              simp only [pure, lookupStorage_result, bind]
              cases stored : state.storage[source.storage]? with
              | none => exact Nat.le_refl _
              | some storage =>
                simp only [stored]
                split <;> simp [ConstructionM.fail, ConstructionM.get, ConstructionM.set, bind, pure,
                  ConstructionResult.finalState]

#print axioms evaluationHistoryLifecycle_mark_named

end Goose.Proofs.ConstructionAcceptedExecution
