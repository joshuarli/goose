import Goose.Proofs.ConstructionExitReservationCaptured

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

def ReservationReferencesBounded (state : ConstructionState) (ambient : OwnershipAmbient) : Prop :=
  ∀ frame ∈ ambient, (∀ token ∈ frame.tickets, token < state.exitReservations.size) ∧
    match frame with
    | .callChannels activation _ => ∀ token, .completion token ∈ activation.channels → token < state.exitReservations.size
    | .breakTarget target _ => ∀ token, .completion token ∈ target.channels → token < state.exitReservations.size
    | _ => True

theorem initial_reservationReferencesBounded : ReservationReferencesBounded .initial [] := by
  intro frame member
  simp at member

theorem reservationReferencesBounded_unreferenced (state : ConstructionState) (ambient : OwnershipAmbient)
    (valid : ReservationReferencesBounded state ambient) :
    ReservationTokenUnreferenced state.exitReservations.size ambient := by
  intro frame member
  have bounded := valid frame member
  refine ⟨?_, ?_⟩
  · intro owned
    exact Nat.lt_irrefl _ (bounded.1 _ owned)
  · cases frame <;> try trivial
    all_goals intro found; exact Nat.lt_irrefl _ (bounded.2 _ found)

theorem wait_completion_references_bounded (state : ConstructionState) (ambient : OwnershipAmbient)
    (incoming : Nat) (channels : List Channel) (carriers : List Goose.Construct.Carrier)
    (valid : ReservationReferencesBounded state ambient) :
    let token := state.exitReservations.size
    let waited := { state with exitReservations := state.exitReservations.push (.waiting incoming) }
    waitExitDestination incoming state = .ok token waited ∧
      ReservationReferencesBounded waited (.completionChannels [token] channels carriers :: ambient) := by
  dsimp only
  constructor
  · simp [waitExitDestination, ConstructionM.get, ConstructionM.set, bind, pure]
  · intro frame member
    rcases List.mem_cons.mp member with same | prior
    · subst frame
      simp [OwnershipAmbientFrame.tickets]
    · obtain ⟨tickets, channelsBounded⟩ := valid frame prior
      refine ⟨?_, ?_⟩
      · intro token owned
        have bound := tickets token owned
        simpa only [Array.size_push] using Nat.lt_succ_of_lt bound
      · cases frame <;> try trivial
        all_goals
          intro token owned
          have bound := channelsBounded token owned
          simpa only [Array.size_push] using Nat.lt_succ_of_lt bound

theorem fresh_reservation_references_bounded (before after : ConstructionState) (ambient : OwnershipAmbient)
    (incoming selected token : Nat) (channels : List Channel) (carriers : List Goose.Construct.Carrier)
    (lifecycle : ReservationLifecycleInvariant before) (valid : ReservationReferencesBounded before ambient)
    (reservation : reserveExitDestination incoming .newValue before = .ok (token, selected) after) :
    ReservationReferencesBounded after (.exitChannels [token] channels carriers :: ambient) := by
  obtain ⟨fresh, snapshot, pushed⟩ := reserveExitDestination_active_push incoming .newValue before after token selected lifecycle reservation
  have size : after.exitReservations.size = before.exitReservations.size + 1 := by simp [pushed]
  intro frame member
  rcases List.mem_cons.mp member with same | prior
  · subst frame
    simp [OwnershipAmbientFrame.tickets, size, fresh]
  · obtain ⟨tickets, channelsBounded⟩ := valid frame prior
    refine ⟨?_, ?_⟩
    · intro id owned
      rw [size]
      exact Nat.lt_succ_of_lt (tickets id owned)
    · cases frame <;> try trivial
      all_goals
        intro id owned
        rw [size]
        exact Nat.lt_succ_of_lt (channelsBounded id owned)

theorem accepted_reservation_captured_from_history (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (row : PendingDestination) (present : before.construction.destinations[incoming]? = some row)
    (opened : row.progress = .open (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (channels : List Channel) (carriers : List Goose.Construct.Carrier)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (history : ReservationReferencesBounded before.construction ambient)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved) :
    ReservationReferencesBounded reserved (.exitChannels [token] channels carriers :: ambient) ∧
    OwnershipCapturedReceivingBounds reserved (.exitChannels [token] channels carriers :: ambient) ∧
    OwnershipCapturedReceivingFrames reserved (.exitChannels [token] channels carriers :: ambient) := by
  have fresh := (accepted_fresh_reservation_frames config initialized before reserved incoming token selected
    ambient types live regions pending world reservation channels carriers).1
  have unreferenced : ReservationTokenUnreferenced token ambient := by
    rw [fresh]
    exact reservationReferencesBounded_unreferenced before.construction ambient history
  have captured := accepted_open_reservation_captured config initialized before reserved incoming selected token count row
    present opened current ambient types live regions pending channels carriers world reservation unreferenced
  exact ⟨fresh_reservation_references_bounded before.construction reserved ambient incoming selected token channels carriers
    world.ownership.source.structural.1.1 history reservation, captured.1, captured.2⟩

#print axioms reservationReferencesBounded_unreferenced
#print axioms wait_completion_references_bounded
#print axioms fresh_reservation_references_bounded
#print axioms accepted_reservation_captured_from_history

end Goose.Proofs.ConstructionAcceptedExecution
