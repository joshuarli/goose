import Goose.Proofs.ConstructionExitDirectFreshAmbient

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership

theorem direct_fresh_context (before : ExecutionState) (incoming : Nat) (row : PendingDestination) (ambient : OwnershipAmbient) (carriers : List Goose.Construct.Carrier)
    (valid : OwnershipExecutionContext before ambient) (history : ReservationReferencesBounded before.construction ambient)
    (present : before.construction.destinations[incoming]? = some row) (opened : row.progress = .open 0)
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (noRetained : completedCarrierIds ambient.retained = []) :
    let waited := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.active .fresh incoming incoming row) } }
    OwnershipExecutionContext waited (.exitChannels [before.construction.exitReservations.size] [] carriers :: ambient) := by
  let state := before.construction
  let waited := { before with construction := { state with exitReservations := state.exitReservations.push (.active .fresh incoming incoming row) } }
  have unreferenced := reservationReferencesBounded_unreferenced state ambient history
  have captured := captured_frames_push_reservation state ambient (.active .fresh incoming incoming row) unreferenced valid.receiving
  have bounds : OwnershipCapturedReceivingBounds waited.construction ambient := by
    have channel (c : Channel) (different : c ≠ .completion state.exitReservations.size)
        (old : OwnershipChannelReceivingBound state c) : OwnershipChannelReceivingBound waited.construction c := by
      cases c with
      | register ty => trivial
      | construct id => exact old
      | completion token =>
        intro id ticket
        have ne : token ≠ state.exitReservations.size := by
          intro same
          subst token
          exact different rfl
        have prior : state.exitReservations[token]? = some (.waiting id) := by
          simpa [waited, Array.getElem?_push, ne] using ticket
        exact old id prior
    have go : ∀ frames : OwnershipAmbient, ReservationTokenUnreferenced state.exitReservations.size frames →
        OwnershipCapturedReceivingBounds state frames → OwnershipCapturedReceivingBounds waited.construction frames := by
      intro frames
      induction frames with
      | nil => intro _ _; trivial
      | cons frame rest ih =>
        intro fresh old
        have head := fresh frame (by simp)
        have tail : ReservationTokenUnreferenced state.exitReservations.size rest := by
          intro item member
          exact fresh item (List.mem_cons_of_mem frame member)
        refine ⟨?_, ih tail old.2⟩
        cases frame <;> try trivial
        case receivingScope capture carriers => exact channel (.construct capture.incoming) (by intro equal; cases equal) old.1
        all_goals
          intro c member
          have ne : c ≠ .completion state.exitReservations.size := by
            intro same
            subst c
            exact head.2 member
          exact channel c ne (old.1 c member)
    exact go ambient unreferenced valid.bounds
  have reservations : OwnershipReservationFrames waited.construction
      (.exitChannels [state.exitReservations.size] [] carriers :: ambient) := by
    intro token reservation present needs
    by_cases same : token = state.exitReservations.size
    · subst token
      exact ⟨.exitChannels [state.exitReservations.size] [] carriers, by simp, by simp [OwnershipAmbientFrame.tickets]⟩
    · have prior : state.exitReservations[token]? = some reservation := by
        simpa [waited, Array.getElem?_push, same] using present
      obtain ⟨frame, member, owns⟩ := valid.reservations token reservation prior needs
      exact ⟨frame, List.mem_cons_of_mem _ member, owns⟩
  change OwnershipExecutionContext waited (.exitChannels [state.exitReservations.size] [] carriers :: ambient)
  refine ⟨?_, ?_, ?_, reservations, ⟨trivial, captured⟩, ⟨trivial, bounds⟩, ?_⟩
  · exact direct_fresh_source_state state incoming row valid.source present opened current
  · exact direct_fresh_ambient state incoming row ambient carriers valid.source valid.retention history present opened current noRetained
  · exact ⟨valid.runtime.activations, valid.runtime.breaks⟩
  · exact ⟨valid.identities.activations, valid.identities.breaks⟩


#print axioms direct_fresh_context
end Goose.Proofs.ConstructionAcceptedExecution
