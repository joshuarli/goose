import Goose.Proofs.ConstructionExecutionProtocolReservationLandingMetadataCompletion
import Goose.Proofs.ConstructionExecutionProtocolReservationLanding

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

theorem commitExitReplacement_reservation_frame (receiving : Option DestinationId)
    (id : DestinationId) (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (commitExitReplacement receiving id state).finalState := by
  simp only [commitExitReplacement, lookupDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some replacement =>
      simp only [present]
      cases progress : replacement.progress <;> try simp only [progress] <;> try exact .refl state
      case built count =>
        simp only [pure, bind, ConstructionM.get]
        cases anchored : exitLandingAnchor (state.destinations.size + 1) id replacement.storage receiving state with
        | fault reason after =>
            have same := exitLandingAnchor_finalState (state.destinations.size + 1) id replacement.storage receiving state
            simp only [anchored, ConstructionResult.finalState] at same
            subst after
            exact .refl state
        | ok value after =>
            rcases value with ⟨old, superseded, chain⟩
            obtain ⟨same, earlier, oldPresent⟩ := exitLandingAnchor_success
              (state.destinations.size + 1) id replacement.storage receiving state after old superseded chain anchored
            subst after
            simp only [bind]
            have owner : match superseded.use with
                | .receiver => True
                | .child parent | .replacement parent => parent < id := by
              have prior := valid.2.2.2 old superseded oldPresent
              cases oldUse : superseded.use with
              | receiver => trivial
              | child parent | replacement parent =>
                  exact Nat.lt_trans (by simpa only [oldUse] using prior) earlier
            have finish (update : Option (DestinationId × PendingDestination))
                (parentValid : ∀ parentId parent, update = some (parentId, parent) →
                  ∃ before, state.destinations[parentId]? = some before ∧
                    ReservationProgressPreserves before.progress parent.progress ∧ parentId < old) :
                ReservationMetadataFrame state (((do
                  completedStep id old count replacement superseded update
                  let final ← ConstructionM.get
                  ConstructionM.set { final with destinationSuccessors := chain.map (fun previous => (previous, id)) ++ final.destinationSuccessors }) : ConstructionM Unit) state).finalState := by
              have preserved := completedStep_reservation_frame state id old count replacement superseded update
                present progress owner parentValid earlier valid
              cases completed : completedStep id old count replacement superseded update state with
              | fault reason final =>
                  simpa only [completed, bind, ConstructionResult.finalState] using preserved
              | ok value final =>
                  simp only [completed, ConstructionResult.finalState] at preserved
                  simpa only [completed, bind, ConstructionM.get, ConstructionM.set, ConstructionResult.finalState] using
                    preserved.trans (reservationMetadataFrame_successors final
                      (chain.map (fun previous => (previous, id)) ++ final.destinationSuccessors))
            cases oldUse : superseded.use with
            | receiver => exact finish none (by intro parentId parent impossible; cases impossible)
            | child parentId | replacement parentId =>
                simp only [lookupDestination_result, bind]
                cases parentPresent : state.destinations[parentId]? with
                | none => exact .refl state
                | some parent =>
                    simp only [parentPresent]
                    cases parentProgress : parent.progress <;> try simp only [parentProgress] <;> try exact .refl state
                    all_goals
                      split
                      · exact .refl state
                      · apply finish
                        intro index updated selected
                        cases selected
                        refine ⟨parent, parentPresent, ?_, ?_⟩
                        · simp [ReservationProgressPreserves, parentProgress, ReservationStableProgress]
                        · simpa only [oldUse] using valid.2.2.2 old superseded oldPresent


theorem landExitReplacementChain_reservation_frame (id : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (landExitReplacementChain id state).finalState :=
  commitExitReplacement_reservation_frame none id state valid

theorem landExitReplacementInto_reservation_frame (receiving id : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (landExitReplacementInto receiving id state).finalState :=
  commitExitReplacement_reservation_frame (some receiving) id state valid

theorem landExitReplacementChain_reservation_lifecycle (id : DestinationId)
    (state : ConstructionState) (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant (landExitReplacementChain id state).finalState :=
  ⟨landExitReplacementChain_destination_lifecycle_invariant id state valid.1,
    destinationReservationStateValid_frame state _
      (landExitReplacementChain_reservation_frame id state valid.1) valid.2⟩

theorem landExitReplacementInto_reservation_lifecycle (receiving id : DestinationId)
    (state : ConstructionState) (valid : ReservationLifecycleInvariant state) :
    ReservationLifecycleInvariant (landExitReplacementInto receiving id state).finalState :=
  ⟨landExitReplacementInto_destination_lifecycle_invariant receiving id state valid.1,
    destinationReservationStateValid_frame state _
      (landExitReplacementInto_reservation_frame receiving id state valid.1) valid.2⟩

#print axioms commitExitReplacement_reservation_frame
#print axioms landExitReplacementChain_reservation_frame
#print axioms landExitReplacementInto_reservation_frame
#print axioms landExitReplacementChain_reservation_lifecycle
#print axioms landExitReplacementInto_reservation_lifecycle

end Goose.Proofs.ConstructionExecutionProtocol
