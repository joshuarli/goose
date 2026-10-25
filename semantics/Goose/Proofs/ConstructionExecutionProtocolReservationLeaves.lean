import Goose.Proofs.ConstructionExecutionProtocolReservationFrames
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

local syntax "reservation_split_if" : tactic
elab_rules : tactic
  | `(tactic| reservation_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no reservation condition to split"
      return [yes.mvarId, no.mvarId]

theorem adaptDestinationType_reservation_frame (id : DestinationId) (logicalType : Goose.Construct.Ty)
    (state : ConstructionState) :
    ReservationMetadataFrame state (adaptDestinationType id logicalType state).finalState := by
  simp only [adaptDestinationType, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          cases progress : destination.progress <;> try simp only [progress] <;> try exact .refl state
          all_goals
            try simp only [pure, bind]
            reservation_split_if
            · exact .refl state
            · have inside := (Array.getElem?_eq_some_iff.mp present).choose
              simp only [replaceDestination_result, inside, ↓reduceIte]
              exact reservationMetadataFrame_replace state id destination _ present (by simp only [progress])

theorem restoreReceivingLayout_reservation_frame (id : DestinationId) (layout : ReceivingLayout)
    (state : ConstructionState) :
    ReservationMetadataFrame state (restoreReceivingLayout id layout state).finalState := by
  simp only [restoreReceivingLayout, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          cases progress : destination.progress <;> try simp only [progress] <;> try exact .refl state
          case built count =>
            try simp only [pure, bind]
            reservation_split_if
            · exact .refl state
            · have inside := (Array.getElem?_eq_some_iff.mp present).choose
              simp only [replaceDestination_result, inside, ↓reduceIte]
              exact reservationMetadataFrame_replace state id destination _ present (by simp only [progress])

theorem recordCopy_reservation_frame (source : CopySource) (id : DestinationId)
    (state : ConstructionState) : ReservationMetadataFrame state (recordCopy source id state).finalState := by
  simp only [recordCopy, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          cases progress : destination.progress <;> try simp only [progress] <;> try exact .refl state
          case «open» count =>
            have finish : ReservationMetadataFrame state { state with events := state.events ++ [.copy source id] } := by
              apply reservationMetadataFrame_emit_mutable state id destination _ present
              · simp only [progress, ReservationStableProgress, not_false_eq_true]
              · intro queried different
                simp [destinationObservations, observeDestination, Ne.symm different]
            cases source with
            | storage sourceId path =>
                simp only [lookupStorage_result, bind]
                cases stored : state.storage[sourceId]? with
                | none => exact .refl state
                | some storage => simpa only [pure, bind, emit_result, ConstructionResult.finalState] using finish
            | «repeat» sourceId =>
                simp only [lookupDestination_result, bind]
                cases stored : state.destinations[sourceId]? with
                | none => exact .refl state
                | some sourceDestination =>
                    simp only [stored]
                    cases sourceProgress : sourceDestination.progress <;>
                      simp only [sourceProgress, pure, bind, emit_result, ConstructionResult.finalState] <;>
                      first | exact .refl state | exact finish

theorem stageDestination_reservation_frame (id : DestinationId) (state : ConstructionState) :
    ReservationMetadataFrame state (stageDestination id state).finalState := by
  simp only [stageDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          cases progress : destination.progress <;> try simp only [progress] <;> try exact .refl state
          case «open» count =>
            cases count <;> try exact .refl state
            case zero =>
              cases layout : destination.layout <;> try simp only [layout] <;> try exact .refl state
              case limited capacity slotBytes =>
                cases backing : destination.backing <;> try simp only [backing] <;> try exact .refl state
                case direct receiver =>
                  cases known : destination.knownCount <;> try simp only [known] <;> try exact .refl state
                  case none =>
                    cases use : destination.use <;> try simp only [use] <;> try exact .refl state
                    case receiver =>
                      simp only [reserveStorage, ConstructionM.get, ConstructionM.set, bind,
                        pure, replaceDestination_result, inside, ↓reduceIte, emit_result, ConstructionResult.finalState]
                      apply reservationMetadataFrame_replace_events state id destination _ _ [.stage id] present
                      · simp
                      · intro queried different
                        simp [destinationObservations, observeDestination, Ne.symm different]
                      · intro stable
                        simp only [progress, ReservationStableProgress] at stable

end Goose.Proofs.ConstructionExecutionProtocol
