import Goose.Proofs.ConstructionExitDirectSourceRoles
import Goose.Proofs.ConstructionExecutionProtocolReservationReserve
import Goose.Proofs.ConstructionExitReservationHistory

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem waitExitDestination_source_state (state : ConstructionState) (incoming : Nat)
    (source : OwnershipSourceState state) :
    OwnershipSourceState (waitExitDestination incoming state).finalState := by
  let waited := { state with exitReservations := state.exitReservations.push (.waiting incoming) }
  have active (token oldIncoming selected : Nat) (snapshot : PendingDestination)
      (ticket : waited.exitReservations[token]? = some (.active .fresh oldIncoming selected snapshot)) :
      state.exitReservations[token]? = some (.active .fresh oldIncoming selected snapshot) := by
    simp only [waited, Array.getElem?_push] at ticket
    split at ticket
    · cases ticket
    · exact ticket
  have lifecycle := waitExitDestination_reservation_lifecycle incoming state source.structural.1.1
  change ReservationLifecycleInvariant waited at lifecycle
  have roles : LiveFreshReservationSuccessorRoles waited := by
    intro token oldIncoming selected node snapshot row ticket path present
    exact source.aliases token oldIncoming selected node snapshot row (active token oldIncoming selected snapshot ticket)
      (DestinationSuccessorPath.congr (before := waited) (after := state) rfl path) present
  have links : ConstructionOwnershipLinks waited := by
    have previous := source.structural.1.2.1
    refine ⟨previous.1, previous.2.1, ?_, ?_, ?_, ?_, previous.2.2.2.2.2.2⟩
    · constructor
      · intro token oldIncoming selected snapshot ticket
        exact previous.2.2.1.1 token oldIncoming selected snapshot (active token oldIncoming selected snapshot ticket)
      · exact previous.2.2.1.2
    · intro token oldIncoming selected snapshot ticket
      exact previous.2.2.2.1 token oldIncoming selected snapshot (active token oldIncoming selected snapshot ticket)
    · intro token oldIncoming selected snapshot row ticket different found n replacement progress
      exact previous.2.2.2.2.1 token oldIncoming selected snapshot row
        (active token oldIncoming selected snapshot ticket) different found n replacement progress
    · intro token oldIncoming selected snapshot ticket direct
      exact previous.2.2.2.2.2.1 token oldIncoming selected snapshot (active token oldIncoming selected snapshot ticket) direct
  have supportBefore : ∀ id, ReplacementSupported waited id → ReplacementSupported state id := by
    intro id supported
    induction supported with
    | active id row found phase => exact .active id row found phase
    | parent id parent row found use supported ih => exact .parent id parent row found use ih
  have support : SupportedReplacementAuthority waited := by
    intro id parent row found use supported
    exact source.structural.1.2.2.1 id parent row found use (supportBefore id supported)
  have unsupported : UnsupportedResumptionKeys waited := by
    intro id snapshot found supported
    exact source.structural.1.2.2.2.2.1 id snapshot found (supportBefore id supported)
  have resumptions : ResumptionReservationRoles waited := by
    intro key saved found token oldIncoming selected snapshot ticket resolved
    rw [destinationCurrent_congr_tables state waited rfl rfl selected] at resolved
    exact source.resumptionRoles key saved found token oldIncoming selected snapshot
      (active token oldIncoming selected snapshot ticket) resolved
  change OwnershipSourceState waited
  exact ⟨⟨⟨lifecycle, links, support, source.structural.1.2.2.2.1, unsupported,
    liveFreshReservationSuccessorRoles_current waited roles⟩, source.structural.2.1,
    liveFreshReservationSuccessorRoles_raw waited roles⟩, roles, source.inactiveKeys, resumptions⟩

theorem waitExitDestination_ambient (state : ConstructionState) (incoming : Nat) (ambient : OwnershipAmbient)
    (source : OwnershipSourceState state) (valid : OwnershipAmbientInvariant state ambient) :
    OwnershipAmbientInvariant (waitExitDestination incoming state).finalState
      (.completionChannels [state.exitReservations.size] [] [] :: ambient) := by
  let waited := { state with exitReservations := state.exitReservations.push (.waiting incoming) }
  have sourceAfter := waitExitDestination_source_state state incoming source
  change OwnershipSourceState waited at sourceAfter
  have active (token oldIncoming selected : Nat) (snapshot : PendingDestination)
      (ticket : waited.exitReservations[token]? = some (.active .fresh oldIncoming selected snapshot)) :
      state.exitReservations[token]? = some (.active .fresh oldIncoming selected snapshot) := by
    simp only [waited, Array.getElem?_push] at ticket
    split at ticket
    · cases ticket
    · exact ticket
  have supportBefore : ∀ id, ReplacementSupported waited id → ReplacementSupported state id := by
    intro id supported
    induction supported with
    | active id row found phase => exact .active id row found phase
    | parent id parent row found use supported ih => exact .parent id parent row found use ih
  have boundaries : ∀ frames : OwnershipAmbient, OwnershipAmbientBoundaries state frames →
      OwnershipAmbientBoundaries waited frames := by
    intro frames
    induction frames with
    | nil => intro _; trivial
    | cons frame rest ih =>
      intro old
      refine ⟨?_, ih old.2⟩
      intro token oldIncoming selected current snapshot owned ticket resolved retained member
      rw [destinationCurrent_congr_tables state waited rfl rfl selected] at resolved
      exact old.1 token oldIncoming selected current snapshot owned (active token oldIncoming selected snapshot ticket) resolved retained member
  change OwnershipAmbientInvariant waited (.completionChannels [state.exitReservations.size] [] [] :: ambient)
  refine ⟨sourceAfter.structural.1, ?_, ?_, boundaries ambient valid.boundaries⟩
  · intro id row found inactive supported
    obtain ⟨retained, member, ancestry⟩ := valid.anchors id row found inactive (supportBefore id supported)
    exact ⟨retained, by simpa [OwnershipAmbient.retained, OwnershipAmbientFrame.carriers, completedCarrierIds] using member, ancestry⟩
  · intro token oldIncoming selected current snapshot owned ticket resolved retained member
    simp only [OwnershipAmbientFrame.tickets, List.mem_singleton] at owned
    subst token
    simp [waited] at ticket

#print axioms waitExitDestination_ambient

theorem captured_frames_push_reservation (state : ConstructionState) (ambient : OwnershipAmbient)
    (appended : ExitReservation)
    (unreferenced : ReservationTokenUnreferenced state.exitReservations.size ambient)
    (valid : OwnershipCapturedReceivingFrames state ambient) :
    OwnershipCapturedReceivingFrames { state with exitReservations := state.exitReservations.push appended } ambient := by
  let after := { state with exitReservations := state.exitReservations.push appended }
  have oldTicket (token : Nat) (reservation : ExitReservation) (different : token ≠ state.exitReservations.size)
      (present : after.exitReservations[token]? = some reservation) : state.exitReservations[token]? = some reservation := by
    simpa [after, Array.getElem?_push, different] using present
  have within (outer : OwnershipAmbient) (outerUnreferenced : ∀ frame ∈ outer, state.exitReservations.size ∉ frame.tickets)
      (receiving : Nat) (previous : OwnershipReceivingWithinSuccessorFrames state outer receiving) :
      OwnershipReceivingWithinSuccessorFrames after outer receiving := by
    intro frame member token owned oldIncoming reserved saved node ticket aliases ancestry
    have different : token ≠ state.exitReservations.size := by
      intro same
      subst token
      exact outerUnreferenced frame member owned
    have original := oldTicket token (.active .fresh oldIncoming reserved saved) different ticket
    exact previous frame member token owned oldIncoming reserved saved node original
      (DestinationSuccessorPath.congr (before := after) (after := state) rfl aliases) ancestry
  have channel (outer : OwnershipAmbient) (outerUnreferenced : ∀ frame ∈ outer, state.exitReservations.size ∉ frame.tickets)
      (channel : Channel) (different : channel ≠ .completion state.exitReservations.size)
      (previous : OwnershipChannelReceivingWithinFrames state outer channel) :
      OwnershipChannelReceivingWithinFrames after outer channel := by
    have currentBefore (id receiving : Nat) (current : destinationCurrent after id = .ok receiving) :
        destinationCurrent state id = .ok receiving := by
      rw [destinationCurrent_congr_tables state after rfl rfl id] at current
      exact current
    cases channel with
    | register ty => trivial
    | construct id =>
      intro receiving current
      exact within outer outerUnreferenced receiving (previous receiving (currentBefore id receiving current))
    | completion token =>
      have ne : token ≠ state.exitReservations.size := by
        intro same
        subst token
        exact different rfl
      constructor
      · intro id ticket receiving current
        exact within outer outerUnreferenced receiving (previous.1 id (oldTicket token (.waiting id) ne ticket) receiving (currentBefore id receiving current))
      · intro oldRole id reserved saved ticket receiving current
        exact within outer outerUnreferenced receiving (previous.2 oldRole id reserved saved
          (oldTicket token (.active oldRole id reserved saved) ne ticket) receiving (currentBefore reserved receiving current))
  induction ambient with
  | nil => trivial
  | cons frame outer ih =>
    have head := unreferenced frame (by simp)
    have rest : ReservationTokenUnreferenced state.exitReservations.size outer := by
      intro item member
      exact unreferenced item (List.mem_cons_of_mem frame member)
    have outside : ∀ item ∈ outer, state.exitReservations.size ∉ item.tickets := by
      intro item member
      exact (rest item member).1
    refine ⟨?_, ih rest valid.2⟩
    cases frame <;> try trivial
    case receivingScope capture carriers =>
      exact channel outer outside (.construct capture.incoming) (by intro equal; cases equal) valid.1
    all_goals
      intro c member
      have different : c ≠ .completion state.exitReservations.size := by
        intro same
        subst c
        exact head.2 member
      exact channel outer outside c different (valid.1 c member)




theorem captured_frames_push_waiting (state : ConstructionState) (ambient : OwnershipAmbient)
    (incoming : Nat)
    (unreferenced : ReservationTokenUnreferenced state.exitReservations.size ambient)
    (valid : OwnershipCapturedReceivingFrames state ambient) :
    OwnershipCapturedReceivingFrames { state with exitReservations := state.exitReservations.push (.waiting incoming) } ambient := by
  exact captured_frames_push_reservation state ambient (.waiting incoming) unreferenced valid

theorem waitExitDestination_context (before : ExecutionState) (incoming : Nat) (ambient : OwnershipAmbient)
    (valid : OwnershipExecutionContext before ambient) (history : ReservationReferencesBounded before.construction ambient) :
    let waited := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.waiting incoming) } }
    OwnershipExecutionContext waited (.completionChannels [before.construction.exitReservations.size] [] [] :: ambient) := by
  let state := before.construction
  let waited := { before with construction := { state with exitReservations := state.exitReservations.push (.waiting incoming) } }
  have unreferenced := reservationReferencesBounded_unreferenced state ambient history
  have captured := captured_frames_push_waiting state ambient incoming unreferenced valid.receiving
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
      (.completionChannels [state.exitReservations.size] [] [] :: ambient) := by
    intro token reservation present needs
    by_cases same : token = state.exitReservations.size
    · subst token
      exact ⟨.completionChannels [state.exitReservations.size] [] [], by simp, by simp [OwnershipAmbientFrame.tickets]⟩
    · have prior : state.exitReservations[token]? = some reservation := by
        simpa [waited, Array.getElem?_push, same] using present
      obtain ⟨frame, member, owns⟩ := valid.reservations token reservation prior needs
      exact ⟨frame, List.mem_cons_of_mem _ member, owns⟩
  change OwnershipExecutionContext waited (.completionChannels [state.exitReservations.size] [] [] :: ambient)
  refine ⟨?_, ?_, ?_, reservations, ⟨trivial, captured⟩, ⟨trivial, bounds⟩, ?_⟩
  · exact waitExitDestination_source_state state incoming valid.source
  · exact waitExitDestination_ambient state incoming ambient valid.source valid.retention
  · exact ⟨valid.runtime.activations, valid.runtime.breaks⟩
  · exact ⟨valid.identities.activations, valid.identities.breaks⟩

#print axioms captured_frames_push_reservation
#print axioms waitExitDestination_context

#print axioms captured_frames_push_waiting

#print axioms waitExitDestination_source_state

end Goose.Proofs.ConstructionAcceptedExecution
