import Goose.Proofs.ConstructionExitCompletionActivation
import Goose.Proofs.ConstructionExitBlockedParent

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionStorage

theorem openChild_open_receiver (before after : ConstructionState) (parentId child : Nat)
    (ty : Goose.Construct.Ty) (layout : ReceivingLayout)
    (executed : openChild parentId ty layout before = .ok child after) :
    ∃ parent snapshot count, after.destinations[parentId]? = some parent ∧
      parent.progress = .suspended count child ∧ after.destinations[child]? = some snapshot ∧
      snapshot.use = .child parentId ∧ snapshot.progress = .open 0 := by
  simp only [openChild, writableDestination_result, bind] at executed
  cases present : before.destinations[parentId]? with
  | none => simp [present] at executed
  | some parent =>
    simp only [present] at executed
    cases allowed : destinationCanWrite before parentId with
    | false => simp [allowed] at executed
    | true =>
      simp only [allowed] at executed
      cases progress : parent.progress <;> simp only [progress] at executed <;> try contradiction
      case «open» count =>
        simp only [lookupStorage_result, bind] at executed
        cases stored : before.storage[parent.storage]? with
        | none => simp [stored] at executed
        | some storage =>
          simp only [stored] at executed
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
          simp only [ConstructionM.get, ConstructionM.set, pure, bind,
            replaceDestination_result, replaceStorage_result, emit_result,
            Array.size_push, Nat.lt_succ_of_lt inside, storageInside,
            Array.size_setIfInBounds, ↓reduceIte] at executed
          split at executed
          · contradiction
          · split at executed <;>
              simp only [Nat.lt_succ_of_lt inside, storageInside, ↓reduceIte, bind, pure] at executed <;>
              cases executed <;>
              simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self,
                Array.getElem?_setIfInBounds_ne (Nat.ne_of_lt inside), Array.getElem?_push,
                Nat.ne_of_lt inside]
            all_goals exact ⟨_, ⟨Nat.lt_succ_of_lt inside, rfl⟩, count, rfl⟩

theorem completion_write_fresh_reservation (state : ExecutionState) (source : RuntimeActivation)
    (completion incoming parentId parentCount : Nat) (snapshot parent : PendingDestination)
    (ty : Goose.Construct.Ty) (bytes : List UInt8) (origin : OriginId) (payload : ByteArray)
    (waiting : state.construction.exitReservations[completion]? = some (.waiting incoming))
    (present : state.construction.destinations[incoming]? = some snapshot) (opened : snapshot.progress = .open 0)
    (current : destinationCurrent state.construction incoming = .ok incoming)
    (childUse : snapshot.use = .child parentId)
    (parentFound : state.construction.destinations[parentId]? = some parent)
    (parentPhase : parent.progress = .suspended parentCount incoming)
    (lifecycle : ReservationLifecycleInvariant state.construction) (written reserved : ConstructionState)
    (write : writeElement incoming payload { state.construction with
      exitReservations := state.construction.exitReservations.set! completion (.active .fresh incoming incoming snapshot) } = .ok () written)
    (token selected : Nat)
    (reservation : reserveExitDestination incoming .newValue written = .ok (token, selected) reserved) :
    ∃ activated,
      selectCompletionChannel source (.bytes ty bytes origin) (.completion completion) state = .ok (.construct incoming) activated ∧
      reserved.exitReservations[completion]? = some (.active .fresh incoming incoming snapshot) ∧
      token ≠ completion ∧
      written.destinations[parentId]? = some parent ∧ parent.progress = .suspended parentCount incoming := by
  let activated := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! completion (.active .fresh incoming incoming snapshot) } }
  have selectedCompletion := selectWaiting_open_child_direct state.construction completion incoming snapshot waiting present opened current
  have life := selectWaitingExitDestination_reservation_lifecycle completion .newValue state.construction lifecycle
  rw [selectedCompletion] at life
  have frame := writeElement_reservation_frame incoming payload activated.construction life.1
  rw [write] at frame
  simp only [ConstructionResult.finalState] at frame
  have destLife := writeElement_destination_lifecycle_invariant incoming payload activated.construction life.1
  rw [write] at destLife
  simp only [ConstructionResult.finalState] at destLife
  have writtenLife : ReservationLifecycleInvariant written :=
    ⟨destLife, destinationReservationStateValid_frame activated.construction written frame life.2⟩
  have indexing := writeElement_preserves_indexing incoming payload activated.construction
  rw [write] at indexing
  simp only [ConstructionResult.finalState] at indexing
  have activatedCurrent : destinationCurrent activated.construction incoming = .ok incoming := by
    simpa only [activated, destinationCurrent_congr_tables state.construction
      { state.construction with exitReservations := state.construction.exitReservations.set! completion (.active .fresh incoming incoming snapshot) }
      rfl rfl incoming] using current
  have writtenCurrent : destinationCurrent written incoming = .ok incoming := by
    rw [destinationCurrent_result, destinationCurrentSteps_same_indexing _ activated.construction written indexing.1 indexing.2, indexing.1]
    simpa only [destinationCurrent_result] using activatedCurrent
  obtain ⟨actual, actualSelection, ticket, parentAfter, parentPhaseAfter, childAfter⟩ :=
    completion_open_child_write_activates_ticket state source completion incoming parentId parentCount snapshot parent ty bytes origin payload
      waiting present opened current childUse parentFound parentPhase lifecycle written write
  have ticketBound := (Array.getElem?_eq_some_iff.mp ticket).1
  have ticketFrame := reserveExitDestination_fresh_tickets incoming written writtenLife
  rw [reservation] at ticketFrame
  simp only [ConstructionResult.finalState] at ticketFrame
  have reservedTicket : reserved.exitReservations[completion]? = some (.active .fresh incoming incoming snapshot) := by
    rcases ticketFrame with same | ⟨next, saved, appended, _⟩
    · simpa only [same] using ticket
    · simpa [appended, Array.getElem?_push, ticketBound, Nat.ne_of_lt ticketBound] using ticket
  have newTicket := (reserve_open_receiver_snapshot written reserved incoming selected token 0
    { snapshot with progress := .open 1, writeEnd := snapshot.writeEnd + payload.size } childAfter rfl writtenCurrent reservation).2
  have distinct : token ≠ completion := by
    intro same
    subst token
    rw [reservedTicket] at newTicket
    have equal := Option.some.inj newTicket
    have progress := congrArg (fun t : ExitReservation => match t with | .active _ _ _ row => row.progress | _ => .abandoned) equal
    simp [opened] at progress
  exact ⟨actual, actualSelection, reservedTicket, distinct, parentAfter, parentPhaseAfter⟩

#print axioms completion_write_fresh_reservation
#print axioms openChild_open_receiver

end Goose.Proofs.ConstructionAcceptedExecution
