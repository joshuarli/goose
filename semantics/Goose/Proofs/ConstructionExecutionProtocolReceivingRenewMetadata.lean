import Goose.Proofs.ConstructionExecutionProtocolReceivingRenew
import Goose.Proofs.ConstructionExecutionProtocolReceivingRenewMetadataProgress
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

private theorem receivingRenewal_metadata_allocate (state : ConstructionState) (id : DestinationId)
    (snapshot : PendingDestination) (writeEnd : Nat) (storage : Array ReceivingStorage)
    (size : storage.size = state.storage.size)
    (bounds : SavedDestinationBounds state id snapshot)
    (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state { state with
      destinations := state.destinations.push (receivingRenewal snapshot state.destinations.size writeEnd)
      storage := storage
      events := state.events ++ receivingRenewalEvents snapshot state.destinations.size
      destinationSuccessors := (id, state.destinations.size) :: state.destinationSuccessors } := by
  let allocated : ConstructionState := { state with
    destinations := state.destinations.push (receivingRenewal snapshot state.destinations.size writeEnd)
    storage := storage
    events := state.events ++ receivingRenewalEvents snapshot state.destinations.size }
  have frame : ReservationMetadataFrame state allocated := by
    apply reservationMetadataFrame_push state _ storage _ (Nat.le_of_eq size.symm)
    intro queried inside
    cases backing : snapshot.backing <;>
      simp [receivingRenewalEvents, backing, destinationObservations, observeDestination,
        Nat.ne_of_lt inside, (Nat.ne_of_lt inside).symm]
  exact frame.trans (reservationMetadataFrame_successors allocated
    ((id, state.destinations.size) :: state.destinationSuccessors))

private theorem receivingRenewal_metadata_allocate_owner (state : ConstructionState) (id parent : DestinationId)
    (snapshot before after : PendingDestination) (writeEnd : Nat) (storage : Array ReceivingStorage)
    (size : storage.size = state.storage.size)
    (bounds : SavedDestinationBounds state id snapshot)
    (present : state.destinations[parent]? = some before)
    (capability : after.capability.id = before.capability.id)
    (backing : after.backing = before.backing) (use : after.use = before.use)
    (transition : ReservationProgressPreserves before.progress after.progress)
    (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state { state with
      destinations := (state.destinations.push (receivingRenewal snapshot state.destinations.size writeEnd)).set! parent after
      storage := storage
      events := state.events ++ receivingRenewalEvents snapshot state.destinations.size
      destinationSuccessors := (id, state.destinations.size) :: state.destinationSuccessors } := by
  let allocated : ConstructionState := { state with
    destinations := state.destinations.push (receivingRenewal snapshot state.destinations.size writeEnd)
    storage := storage
    events := state.events ++ receivingRenewalEvents snapshot state.destinations.size
    destinationSuccessors := (id, state.destinations.size) :: state.destinationSuccessors }
  have inside := (Array.getElem?_eq_some_iff.mp present).choose
  have allocatedFrame : ReservationMetadataFrame state allocated :=
    receivingRenewal_metadata_allocate state id snapshot writeEnd storage size bounds valid
  have parentPresent : allocated.destinations[parent]? = some before := by
    simpa only [allocated, Array.getElem?_push, Nat.ne_of_lt inside, ↓reduceIte] using present
  exact allocatedFrame.trans (reservationMetadataFrame_replace_progress allocated parent before after parentPresent transition)

local syntax "renew_split_if" : tactic
elab_rules : tactic
  | `(tactic| renew_split_if) =>
      Lean.Elab.Tactic.liftMetaTactic fun goal => do
        let some (yes, no) ← Lean.Meta.splitIfTarget? goal
          | Lean.throwError "no renewal condition to split"
        return [yes.mvarId, no.mvarId]

set_option maxHeartbeats 3000000 in
theorem renewReceivingDestination_reservation_frame
    (incoming : DestinationId) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state)
    (resumptions : DestinationResumptionsValid state) :
    ReservationMetadataFrame state (renewReceivingDestination incoming state).finalState := by
  simp only [renewReceivingDestination, ConstructionM.get, bind]
  cases resolved : destinationCurrent state incoming with
  | error kind => exact .refl state
  | ok id =>
      simp only [pure, lookupDestination_result, bind]
      cases present : state.destinations[id]? with
      | none => exact .refl state
      | some destination =>
          simp only [present]
          cases progress : destination.progress <;> simp only [progress]
          all_goals try exact .refl state
          all_goals
            try simp only [ConstructionM.get, bind]
            cases saved : state.destinationResumptions.lookup id with
            | none => simp only [saved]; exact .refl state
            | some snapshot =>
                simp only [saved, lookupStorage_result, bind]
                have bounds := resumptions.lookup state id snapshot saved
                cases stored : state.storage[snapshot.storage]? with
                | none => simp only [stored]; exact .refl state
                | some storage =>
                    simp only [stored]
                    cases adaptation : snapshot.adaptation <;> simp only [adaptation]
                    all_goals
                      repeat' first
                        | exact .refl state
                        | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                            lookupDestination_result, replaceDestination_result, replaceStorage_result,
                            emit_result, pure, bind, ConstructionResult.finalState,
                            Array.size_push, Array.size_set!, List.append_assoc,
                            bounds.writeStorage, ↓reduceIte]
                        | renew_split_if
                      all_goals
                        cases use : snapshot.use with
                        | receiver =>
                            simp only [use]
                            cases backing : snapshot.backing <;> simp only [backing]
                            all_goals
                              repeat' first
                                | exact .refl state
                                | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                                    replaceStorage_result, emit_result, pure, bind, ConstructionResult.finalState,
                                    Array.size_push, Array.size_set!, List.append_assoc,
                                    bounds.writeStorage, ↓reduceIte]
                                | renew_split_if
                            all_goals
                              have allocate := receivingRenewal_metadata_allocate state id snapshot
                              simp only [receivingRenewal, receivingRenewalEvents, backing, use, adaptation] at allocate
                              apply allocate
                              · simp [Array.set!_eq_setIfInBounds]
                              · exact bounds
                              · exact valid
                        | child parent | replacement parent =>
                            simp only [use, lookupDestination_result, bind]
                            cases parentPresent : state.destinations[parent]? with
                            | none => simp only [parentPresent]; exact .refl state
                            | some owner =>
                                simp only [parentPresent]
                                have inside := (Array.getElem?_eq_some_iff.mp parentPresent).choose
                                have insideAfter := Nat.lt_succ_of_lt inside
                                cases ownerProgress : owner.progress <;> simp only [ownerProgress]
                                all_goals try exact .refl state
                                all_goals
                                  cases backing : snapshot.backing <;> simp only [backing]
                                  all_goals
                                    repeat' first
                                      | exact .refl state
                                      | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                                          replaceDestination_result, replaceStorage_result,
                                          emit_result, pure, bind, ConstructionResult.finalState,
                                          Array.size_push, Array.size_set!, List.append_assoc,
                                          bounds.writeStorage, insideAfter, ↓reduceIte]
                                      | renew_split_if
                                  all_goals
                                    have allocate := receivingRenewal_metadata_allocate_owner state id parent snapshot owner
                                    simp only [receivingRenewal, receivingRenewalEvents, backing, use, adaptation] at allocate
                                    apply allocate
                                    · simp [Array.set!_eq_setIfInBounds]
                                    · exact bounds
                                    · exact parentPresent
                                    · rfl
                                    · rfl
                                    · rfl
                                    · simp [ReservationProgressPreserves, ownerProgress, ReservationStableProgress]
                                    · exact valid

theorem renewReceivingDestination_reservation_lifecycle (incoming : DestinationId)
    (state : ConstructionState) (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant (renewReceivingDestination incoming state).finalState :=
  ⟨renewReceivingDestination_destination_lifecycle_invariant incoming state valid.1 valid.2.resumptions,
    destinationReservationStateValid_frame state _
      (renewReceivingDestination_reservation_frame incoming state valid.1 valid.2.resumptions) valid.2⟩

#print axioms renewReceivingDestination_reservation_frame
#print axioms renewReceivingDestination_reservation_lifecycle

end Goose.Proofs.ConstructionExecutionProtocol
