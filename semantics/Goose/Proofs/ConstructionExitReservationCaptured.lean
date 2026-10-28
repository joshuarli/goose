import Goose.Proofs.ConstructionExitReservationAllocation

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

def ReservationTokenUnreferenced (token : Nat) (ambient : OwnershipAmbient) : Prop :=
  ∀ frame ∈ ambient, token ∉ frame.tickets ∧
    match frame with
    | .callChannels activation _ => .completion token ∉ activation.channels
    | .breakTarget target _ => .completion token ∉ target.channels
    | _ => True

theorem captured_frames_push_active (state : ConstructionState) (ambient : OwnershipAmbient)
    (role : ExitReservationRole) (incoming selected : Nat) (snapshot : PendingDestination)
    (unreferenced : ReservationTokenUnreferenced state.exitReservations.size ambient)
    (valid : OwnershipCapturedReceivingFrames state ambient) :
    OwnershipCapturedReceivingFrames { state with exitReservations := state.exitReservations.push (.active role incoming selected snapshot) } ambient := by
  let after := { state with exitReservations := state.exitReservations.push (.active role incoming selected snapshot) }
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

theorem accepted_open_reservation_captured (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (row : PendingDestination) (present : before.construction.destinations[incoming]? = some row)
    (opened : row.progress = .open (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (channels : List Channel) (carriers : List Goose.Construct.Carrier)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (unreferenced : ReservationTokenUnreferenced token ambient) :
    OwnershipCapturedReceivingBounds reserved (.exitChannels [token] channels carriers :: ambient) ∧
    OwnershipCapturedReceivingFrames reserved (.exitChannels [token] channels carriers :: ambient) := by
  obtain ⟨allocated, replacement, appended, source, bounds, frames⟩ :=
    accepted_open_reservation_allocation config initialized before reserved incoming selected token count row
      present opened current ambient types live regions pending channels carriers world reservation
  have fresh := (accepted_fresh_reservation_frames config initialized before reserved incoming token selected
    ambient types live regions pending world reservation channels carriers).1
  have frame := openExitReplacement_reservation_frame incoming before.construction world.ownership.source.structural.1.1.1
  rw [replacement] at frame
  have size : allocated.exitReservations.size = token := by
    simpa only [ConstructionResult.finalState, ← fresh] using congrArg Array.size frame.tickets
  have noReference : ReservationTokenUnreferenced allocated.exitReservations.size ambient := by
    simpa only [size] using unreferenced
  have captured := captured_frames_push_active allocated ambient .fresh incoming selected row noReference frames
  rw [appended] at bounds ⊢
  exact ⟨bounds, ⟨trivial, captured⟩⟩

#print axioms captured_frames_push_active
#print axioms accepted_open_reservation_captured

end Goose.Proofs.ConstructionAcceptedExecution
