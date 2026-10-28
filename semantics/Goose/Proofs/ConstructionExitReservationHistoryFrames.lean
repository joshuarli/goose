import Goose.Proofs.ConstructionExitReservationHistory
import Goose.Proofs.ConstructionExitCompletionActivation

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership

theorem reservationReferencesBounded_mono (before after : ConstructionState) (ambient : OwnershipAmbient)
    (size : before.exitReservations.size ≤ after.exitReservations.size)
    (valid : ReservationReferencesBounded before ambient) : ReservationReferencesBounded after ambient := by
  intro frame member
  obtain ⟨tickets, channels⟩ := valid frame member
  refine ⟨?_, ?_⟩
  · intro token owned
    exact Nat.lt_of_lt_of_le (tickets token owned) size
  · cases frame <;> try trivial
    all_goals intro token owned; exact Nat.lt_of_lt_of_le (channels token owned) size

theorem reservationReferencesBounded_release (before after : ConstructionState) (ambient : OwnershipAmbient)
    (token : Nat) (valid : ReservationReferencesBounded before ambient)
    (released : releaseExitReservation token before = .ok () after) :
    ReservationReferencesBounded after ambient := by
  simp only [releaseExitReservation, ConstructionM.get, bind] at released
  cases ticket : before.exitReservations[token]? with
  | none => simp [ticket, ConstructionM.fail] at released
  | some status =>
    cases status <;> simp [ticket, ConstructionM.set, ConstructionM.fail, pure, bind] at released <;>
      subst after <;> apply reservationReferencesBounded_mono before _ ambient _ valid <;> simp

theorem reservationReferencesBounded_pop (state : ConstructionState) (frame : OwnershipAmbientFrame)
    (ambient : OwnershipAmbient) (valid : ReservationReferencesBounded state (frame :: ambient)) :
    ReservationReferencesBounded state ambient := by
  intro found member
  exact valid found (List.mem_cons_of_mem frame member)

theorem reservationReferencesBounded_wait_call (state : ConstructionState) (ambient : OwnershipAmbient)
    (incoming : Nat) (activation : RuntimeActivation) (carriers : List Goose.Construct.Carrier)
    (valid : ReservationReferencesBounded state ambient)
    (channels : activation.channels = [.completion state.exitReservations.size]) :
    ∃ waited token,
      waitExitDestination incoming state = .ok token waited ∧
      activation.channels = [.completion token] ∧
      ReservationReferencesBounded waited (.callChannels activation carriers :: ambient) := by
  let token := state.exitReservations.size
  let waited := { state with exitReservations := state.exitReservations.push (.waiting incoming) }
  have waiting := wait_completion_references_bounded state ambient incoming [] [] valid
  have grown : ReservationReferencesBounded waited ambient := by
    apply reservationReferencesBounded_mono state waited ambient _ valid
    simp [waited]
  refine ⟨waited, token, waiting.1, channels, ?_⟩
  intro frame member
  rcases List.mem_cons.mp member with same | rest
  · subst frame
    refine ⟨by simp [OwnershipAmbientFrame.tickets], ?_⟩
    intro id found
    rw [channels] at found
    simp only [List.mem_singleton, Channel.completion.injEq] at found
    subst id
    simp [waited]
  · exact grown frame rest

theorem reservationReferencesBounded_wait_select (state : ExecutionState) (source : RuntimeActivation)
    (ambient : OwnershipAmbient) (incoming : Nat) (snapshot : PendingDestination)
    (ty : Goose.Construct.Ty) (bytes : List UInt8) (origin : OriginId)
    (valid : ReservationReferencesBounded state.construction ambient)
    (present : state.construction.destinations[incoming]? = some snapshot)
    (opened : snapshot.progress = .open 0)
    (current : destinationCurrent state.construction incoming = .ok incoming) :
    let token := state.construction.exitReservations.size
    let waited := { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.push (.waiting incoming) } }
    let activated := { waited with construction := { waited.construction with
      exitReservations := waited.construction.exitReservations.set! token (.active .fresh incoming incoming snapshot) } }
    waitExitDestination incoming state.construction = .ok token waited.construction ∧
    selectCompletionChannel source (.bytes ty bytes origin) (.completion token) waited = .ok (.construct incoming) activated ∧
    ReservationReferencesBounded activated.construction (.completionChannels [token] [] [] :: ambient) := by
  dsimp only
  have execution := wait_then_select_completion_open_byte state source incoming snapshot ty bytes origin present opened current
  have bounded := wait_completion_references_bounded state.construction ambient incoming [] [] valid
  refine ⟨execution.1, execution.2, ?_⟩
  apply reservationReferencesBounded_mono _ _ _ _ bounded.2
  simp

#print axioms reservationReferencesBounded_release
#print axioms reservationReferencesBounded_wait_call
#print axioms reservationReferencesBounded_wait_select

end Goose.Proofs.ConstructionAcceptedExecution
