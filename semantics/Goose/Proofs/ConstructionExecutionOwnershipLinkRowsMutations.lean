import Goose.Proofs.ConstructionExecutionOwnershipLinkRows
import Goose.Proofs.ConstructionExecutionOwnershipLinkMutations
import Goose.Proofs.ConstructionExecutionProtocolQueries
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

local syntax "ownership_rows_split_if" : tactic
elab_rules : tactic
  | `(tactic| ownership_rows_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no ownership row condition to split"
      return [yes.mvarId, no.mvarId]

theorem adaptDestinationType_ownership_rows (state : ConstructionState) (id : DestinationId)
    (ty : Construct.Ty) : OwnershipLinkRowsFrame state (adaptDestinationType id ty state).finalState := by
  simp only [adaptDestinationType, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some row =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          cases progress : row.progress <;> try simp only [progress] <;> try exact .refl state
          all_goals
            repeat' first
              | exact .refl state
              | solve
                | refine ownershipLinkRowsFrame_replace_mutable state id row _ present ?_ ?_ ?_
                  · rfl
                  · cases use : row.use <;> simp [OwnershipLinkBacking, use]
                  · simp [ReservationStableProgress, progress]
              | simp only [replaceDestination_result, inside, ↓reduceIte, bind, pure,
                  ConstructionM.fail, ConstructionResult.finalState]
              | ownership_rows_split_if
              | split

theorem restoreReceivingLayout_ownership_rows (state : ConstructionState) (id : DestinationId)
    (layout : ReceivingLayout) : OwnershipLinkRowsFrame state (restoreReceivingLayout id layout state).finalState := by
  simp only [restoreReceivingLayout, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some row =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          cases progress : row.progress <;> try simp only [progress] <;> try exact .refl state
          case built count =>
            repeat' first
              | exact .refl state
              | solve
                | refine ownershipLinkRowsFrame_replace_mutable state id row _ present ?_ ?_ ?_
                  · rfl
                  · cases use : row.use <;> simp [OwnershipLinkBacking, use]
                  · simp [ReservationStableProgress, progress]
              | simp only [replaceDestination_result, inside, ↓reduceIte, bind, pure,
                  ConstructionM.fail, ConstructionResult.finalState]
              | ownership_rows_split_if
              | split

theorem abandonDestination_ownership_rows (state : ConstructionState) (id : DestinationId) :
    OwnershipLinkRowsFrame state (abandonDestination id state).finalState := by
  simp only [abandonDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some row =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          cases progress : row.progress <;> try simp only [progress] <;> try exact .refl state
          all_goals
            simp only [lookupStorage_result, bind]
            cases stored : state.storage[row.storage]? with
            | none => exact .refl state
            | some storage =>
                have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
                simp only [stored, replaceStorage_result, replaceDestination_result,
                  storageInside, inside, ↓reduceIte, bind, pure, emit_result, ConstructionResult.finalState]
                refine ownershipLinkRowsFrame_replace_terminal state id row _ present ?_ ?_ ?_ rfl (Or.inr (Or.inl rfl))
                · rfl
                · cases use : row.use <;> simp [OwnershipLinkBacking, use]
                · intro count selected
                  simp

theorem finishDestination_ownership_rows (state : ConstructionState) (id : DestinationId)
    (bounded : DestinationLifecycleInvariant state) :
    OwnershipLinkRowsFrame state (finishDestination id state).finalState := by
  simp only [finishDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some row =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          have storageInside := (bounded.2.2.1 id row present).1
          cases progress : row.progress <;> try simp only [progress] <;> try exact .refl state
          case «open» count =>
            have finished := ownershipLinkRowsFrame_replace_mutable state id row
              { row with progress := .built count } present rfl
              (by cases use : row.use <;> simp [OwnershipLinkBacking, use])
              (by simp [ReservationStableProgress, progress])
            have storedFinished : ∀ storage : ReceivingStorage,
                OwnershipLinkRowsFrame state { state with
                  storage := state.storage.set! row.storage storage
                  destinations := state.destinations.set! id { row with progress := .built count } } :=
              fun _ => finished
            cases layout : row.layout <;> simp only [layout]
            all_goals
              simp only [layout] at finished storedFinished
              cases stored : state.storage[row.storage]?
              all_goals
                repeat' first
                  | exact .refl state
                  | exact finished
                  | exact storedFinished _
                  | simp only [lookupStorage_result, stored, replaceStorage_result,
                      replaceDestination_result, inside, storageInside, ↓reduceIte, pure, bind,
                      ConstructionM.fail, ConstructionResult.finalState]
                  | ownership_rows_split_if
                  | split

theorem restoreReceivingLayout_forwardLinks (state : ConstructionState) (id : DestinationId)
    (layout : ReceivingLayout) (valid : DestinationForwardLinks state) :
    DestinationForwardLinks (restoreReceivingLayout id layout state).finalState := by
  simp only [restoreReceivingLayout, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact valid
  | some row =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact valid
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          cases progress : row.progress <;> try simp only [progress] <;> try exact valid
          case built count =>
            repeat' first
              | exact valid
              | solve
                | exact destinationForwardLinks_replace_metadata state id row _ present rfl rfl (by simpa only [progress]) valid
              | simp only [replaceDestination_result, inside, ↓reduceIte, bind, pure,
                  ConstructionM.fail, ConstructionResult.finalState]
              | ownership_rows_split_if
              | split

end Goose.Proofs.ConstructionExecutionOwnership
