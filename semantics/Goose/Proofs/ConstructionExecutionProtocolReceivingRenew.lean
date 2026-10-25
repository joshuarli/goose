import Goose.Proofs.ConstructionExecutionProtocolReceivingRenewAllocation
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

local syntax "renew_split_if" : tactic
elab_rules : tactic
  | `(tactic| renew_split_if) =>
      Lean.Elab.Tactic.liftMetaTactic fun goal => do
        let some (yes, no) ← Lean.Meta.splitIfTarget? goal
          | Lean.throwError "no renewal condition to split"
        return [yes.mvarId, no.mvarId]

set_option maxHeartbeats 3000000 in
theorem renewReceivingDestination_destination_lifecycle_invariant
    (incoming : DestinationId) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state)
    (resumptions : DestinationResumptionsValid state) :
    DestinationLifecycleInvariant (renewReceivingDestination incoming state).finalState := by
  simp only [renewReceivingDestination, ConstructionM.get, bind]
  cases resolved : destinationCurrent state incoming with
  | error kind => exact valid
  | ok id =>
      simp only [pure, lookupDestination_result, bind]
      cases present : state.destinations[id]? with
      | none => exact valid
      | some destination =>
          simp only [present]
          cases progress : destination.progress <;> simp only [progress]
          all_goals try exact valid
          all_goals
            try simp only [ConstructionM.get, bind]
            cases saved : state.destinationResumptions.lookup id with
            | none => simp only [saved]; exact valid
            | some snapshot =>
                simp only [saved, lookupStorage_result, bind]
                have bounds := resumptions.lookup state id snapshot saved
                cases stored : state.storage[snapshot.storage]? with
                | none => simp only [stored]; exact valid
                | some storage =>
                    simp only [stored]
                    cases adaptation : snapshot.adaptation <;> simp only [adaptation]
                    all_goals
                      repeat' first
                        | exact valid
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
                                | exact valid
                                | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                                    replaceStorage_result, emit_result, pure, bind, ConstructionResult.finalState,
                                    Array.size_push, Array.size_set!, List.append_assoc,
                                    bounds.writeStorage, ↓reduceIte]
                                | renew_split_if
                            all_goals
                              have allocate := receivingRenewal_allocate state id snapshot
                              simp only [receivingRenewal, receivingRenewalEvents, backing, use, adaptation] at allocate
                              apply allocate
                              · simp [Array.set!_eq_setIfInBounds]
                              · exact bounds
                              · exact valid
                        | child parent | replacement parent =>
                            simp only [use, lookupDestination_result, bind]
                            cases parentPresent : state.destinations[parent]? with
                            | none => simp only [parentPresent]; exact valid
                            | some owner =>
                                simp only [parentPresent]
                                have inside := (Array.getElem?_eq_some_iff.mp parentPresent).choose
                                have insideAfter := Nat.lt_succ_of_lt inside
                                cases ownerProgress : owner.progress <;> simp only [ownerProgress]
                                all_goals try exact valid
                                all_goals
                                  cases backing : snapshot.backing <;> simp only [backing]
                                  all_goals
                                    repeat' first
                                      | exact valid
                                      | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                                          replaceDestination_result, replaceStorage_result,
                                          emit_result, pure, bind, ConstructionResult.finalState,
                                          Array.size_push, Array.size_set!, List.append_assoc,
                                          bounds.writeStorage, insideAfter, ↓reduceIte]
                                      | renew_split_if
                                  all_goals
                                    have allocate := receivingRenewal_allocate_owner state id parent snapshot owner
                                    simp only [receivingRenewal, receivingRenewalEvents, backing, use, adaptation] at allocate
                                    apply allocate
                                    · simp [Array.set!_eq_setIfInBounds]
                                    · exact bounds
                                    · exact parentPresent
                                    · rfl
                                    · rfl
                                    · rfl
                                    · intro phase matched
                                      cases phase <;> simp [DestinationTracePhase.matchesDestination,
                                        DestinationTracePhase.matchesProgress, ownerProgress] at matched ⊢
                                    · exact valid

#print axioms renewReceivingDestination_destination_lifecycle_invariant

end Goose.Proofs.ConstructionExecutionProtocol
