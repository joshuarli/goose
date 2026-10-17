import Goose.Proofs.ConstructionExecutionProtocolNamedReservationTree
import Goose.Proofs.ConstructionExecutionProtocolReservationNamed

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

abbrev namedReservationReadDestination (id : DestinationId) : ConstructionM PendingDestination := fun state =>
  (fun {left right : ConstructionResult PendingDestination} (_ : left = right) => left)
    (lookupDestination_result id state)

abbrev namedReservationChildStorage (id : StorageId) : ConstructionM ReceivingStorage := fun state =>
  (fun {left right : ConstructionResult ReceivingStorage} (_ : left = right) => left)
    (lookupStorage_result id state)

abbrev namedReservationActive (destination : PendingDestination) : Bool :=
  match destination.progress with
  | .open _ | .suspended _ _ | .built _ | .exiting _ _ => true
  | .published _ | .attached _ | .abandoned | .cancelled | .retired => false

def namedReservationChildren (selected : DestinationId) (parent : PendingDestination)
    (originalCount : Nat) : ConstructionM Unit := do
  match parent.progress with
  | .built count => if count != originalCount then ConstructionM.fail .ownership
  | .suspended count expected =>
    if count != originalCount then ConstructionM.fail .ownership
    let state ← ConstructionM.get
    let current ← match destinationCurrent state expected with
      | .ok id => pure id
      | .error kind => ConstructionM.fail kind
    let child ← namedReservationReadDestination current
    if current != expected || child.use != .child selected ||
        child.backing.receiverStorage != parent.storage then ConstructionM.fail .ownership
    let storage ← namedReservationChildStorage parent.storage
    if parent.writeEnd > storage.bytes.size then ConstructionM.fail .ownership
    match child.backing with
    | .direct _ => if child.rollbackEnd < parent.writeEnd then ConstructionM.fail .ownership
    | .staged _ _ => pure ()
    if namedReservationActive child then abandonTree current
  | _ => ConstructionM.fail .protocol

local syntax "named_children_split_if" : tactic
elab_rules : tactic
  | `(tactic| named_children_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no named child condition to split"
      return [yes.mvarId, no.mvarId]

set_option maxHeartbeats 1000000 in
theorem namedReservationChildren_lifecycle (selected : DestinationId) (parent : PendingDestination)
    (originalCount : Nat) (state : ConstructionState) (present : state.destinations[selected]? = some parent)
    (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant (namedReservationChildren selected parent originalCount state).finalState ∧
      (namedReservationChildren selected parent originalCount state).finalState.destinations[selected]? = some parent := by
  simp only [namedReservationChildren]
  cases progress : parent.progress <;> simp only [progress] <;> try exact ⟨valid, present⟩
  case built count =>
    named_children_split_if <;> exact ⟨valid, present⟩
  case suspended count expected =>
    named_children_split_if
    · exact ⟨valid, present⟩
    · simp only [ConstructionM.get, bind]
      cases resolved : destinationCurrent state expected with
      | error kind => exact ⟨valid, present⟩
      | ok current =>
        simp only [pure, bind, namedReservationReadDestination, lookupDestination_result]
        cases found : state.destinations[current]? with
        | none => exact ⟨valid, present⟩
        | some child =>
          simp only [found]
          named_children_split_if
          · exact ⟨valid, present⟩
          · rename_i guard
            have childUse : child.use = .child selected := by
              apply Classical.byContradiction
              intro different
              exact guard (by simp [different])
            have earlier : selected < current := by
              simpa only [childUse] using valid.1.2.2.2 current child found
            have cleanup : ReservationLifecycleInvariant (abandonTree current state).finalState ∧
                (abandonTree current state).finalState.destinations[selected]? = some parent := by
              constructor
              · exact ⟨abandonTree_destination_lifecycle_invariant current state valid.1,
                  destinationReservationStateValid_frame state _ (abandonTree_reservation_frame current state valid.1) valid.2⟩
              · exact (abandonTree_earlier_destination current selected state earlier valid.1).trans present
            simp only [namedReservationChildStorage, lookupStorage_result, bind]
            cases stored : state.storage[parent.storage]? with
            | none => exact ⟨valid, present⟩
            | some storage =>
              simp only [stored]
              named_children_split_if
              · exact ⟨valid, present⟩
              · cases backing : child.backing <;> simp only [backing]
                all_goals
                  repeat' first
                    | exact ⟨valid, present⟩
                    | exact cleanup
                    | simp only [bind, pure, ConstructionM.fail, ConstructionResult.finalState]
                    | named_children_split_if

theorem namedReservationChildren_success_progress (selected : DestinationId) (parent : PendingDestination)
    (originalCount : Nat) (state after : ConstructionState)
    (success : namedReservationChildren selected parent originalCount state = .ok () after) :
    SavedDestinationProgress parent.progress := by
  cases progress : parent.progress <;> simp only [progress, SavedDestinationProgress] <;> try trivial
  all_goals simp only [namedReservationChildren, progress, ConstructionM.fail] at success
  all_goals cases success

end Goose.Proofs.ConstructionExecutionProtocol
