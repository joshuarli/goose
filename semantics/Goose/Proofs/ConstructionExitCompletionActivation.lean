import Goose.Proofs.ConstructionExitByteChildCompletion
import Goose.Proofs.ConstructionExecutionProtocolReservationFrontier
import Goose.Proofs.ConstructionExecutionProtocolReservationReserve
import Goose.Proofs.ConstructionElementWriteTransition

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionStorage

theorem selectWaiting_open_child_direct (state : ConstructionState) (token incoming : Nat)
    (snapshot : PendingDestination)
    (waiting : state.exitReservations[token]? = some (.waiting incoming))
    (present : state.destinations[incoming]? = some snapshot) (opened : snapshot.progress = .open 0)
    (current : destinationCurrent state incoming = .ok incoming) :
    selectWaitingExitDestination token .newValue state = .ok incoming { state with
      exitReservations := state.exitReservations.set! token (.active .fresh incoming incoming snapshot) } := by
  have renewal : renewReceivingDestination incoming state = .ok incoming state := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, present, opened]
  have frontier : exitFrontierAction (state.destinations.size + 1) incoming state = .ok incoming state :=
    exitFrontier_open state.destinations.size incoming 0 state snapshot present opened
  simp only [selectWaitingExitDestination, ConstructionM.get, waiting, bind, prepareExitDestination_equation,
    show (ExitSource.newValue == ExitSource.namedResult) = false from rfl, Bool.false_eq_true, ↓reduceIte,
    renewal, frontier, lookupDestination_result, present, opened, Bool.true_or, pure, ConstructionM.set]

theorem selectCompletionChannel_open_byte_direct (state : ExecutionState) (source : RuntimeActivation)
    (token incoming : Nat) (snapshot : PendingDestination) (ty : Goose.Construct.Ty) (bytes : List UInt8) (origin : OriginId)
    (waiting : state.construction.exitReservations[token]? = some (.waiting incoming))
    (present : state.construction.destinations[incoming]? = some snapshot) (opened : snapshot.progress = .open 0)
    (current : destinationCurrent state.construction incoming = .ok incoming) :
    selectCompletionChannel source (.bytes ty bytes origin) (.completion token) state =
      .ok (.construct incoming) { state with construction := { state.construction with
        exitReservations := state.construction.exitReservations.set! token (.active .fresh incoming incoming snapshot) } } := by
  have selected := selectWaiting_open_child_direct state.construction token incoming snapshot waiting present opened current
  simp only [selectCompletionChannel, EvalM.get, waiting, exitSource, receivingDestination, liftConstruction,
    current, bind, pure, Bool.false_eq_true, ↓reduceIte, selected]

theorem completion_open_child_write_activates_ticket (state : ExecutionState) (source : RuntimeActivation)
    (completion incoming parentId parentCount : Nat) (snapshot parent : PendingDestination)
    (ty : Goose.Construct.Ty) (bytes : List UInt8) (origin : OriginId) (payload : ByteArray)
    (waiting : state.construction.exitReservations[completion]? = some (.waiting incoming))
    (present : state.construction.destinations[incoming]? = some snapshot) (opened : snapshot.progress = .open 0)
    (current : destinationCurrent state.construction incoming = .ok incoming)
    (childUse : snapshot.use = .child parentId)
    (parentFound : state.construction.destinations[parentId]? = some parent)
    (parentPhase : parent.progress = .suspended parentCount incoming)
    (lifecycle : ReservationLifecycleInvariant state.construction) (written : ConstructionState)
    (write : writeElement incoming payload { state.construction with
      exitReservations := state.construction.exitReservations.set! completion (.active .fresh incoming incoming snapshot) } = .ok () written) :
    ∃ activated,
      selectCompletionChannel source (.bytes ty bytes origin) (.completion completion) state = .ok (.construct incoming) activated ∧
      written.exitReservations[completion]? = some (.active .fresh incoming incoming snapshot) ∧
      written.destinations[parentId]? = some parent ∧ parent.progress = .suspended parentCount incoming ∧
      written.destinations[incoming]? = some { snapshot with progress := .open 1, writeEnd := snapshot.writeEnd + payload.size } := by
  let activated := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! completion (.active .fresh incoming incoming snapshot) } }
  have selected := selectWaiting_open_child_direct state.construction completion incoming snapshot waiting present opened current
  have life := selectWaitingExitDestination_reservation_lifecycle completion .newValue state.construction lifecycle
  rw [selected] at life
  have frame := writeElement_reservation_frame incoming payload activated.construction life.1
  rw [write] at frame
  simp only [ConstructionResult.finalState] at frame
  have activeBefore : activated.construction.exitReservations[completion]? = some (.active .fresh incoming incoming snapshot) := by
    have inside := (Array.getElem?_eq_some_iff.mp waiting).1
    simp [activated, Array.set!_eq_setIfInBounds, inside]
  have activeAfter : written.exitReservations[completion]? = some (.active .fresh incoming incoming snapshot) := by
    simpa only [frame.tickets] using activeBefore
  have childAfter := writeElement_success_destination incoming payload activated.construction written snapshot 0 present opened write
  have earlier : parentId < incoming := by simpa only [childUse] using lifecycle.1.2.2.2 incoming snapshot present
  have parentAfter : written.destinations[parentId]? = some parent := by
    have transition := writeElement_transition incoming payload activated.construction
    rw [write] at transition
    cases transition with
    | written actual storage count found stored progress =>
      simpa only [activated, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm (Nat.ne_of_lt earlier))] using parentFound
  exact ⟨activated, selectCompletionChannel_open_byte_direct state source completion incoming snapshot ty bytes origin waiting present opened current,
    activeAfter, parentAfter, parentPhase, by simpa only [Nat.zero_add] using childAfter.1⟩

theorem wait_then_select_completion_open_byte (state : ExecutionState) (source : RuntimeActivation)
    (incoming : Nat) (snapshot : PendingDestination) (ty : Goose.Construct.Ty)
    (bytes : List UInt8) (origin : OriginId)
    (present : state.construction.destinations[incoming]? = some snapshot)
    (opened : snapshot.progress = .open 0)
    (current : destinationCurrent state.construction incoming = .ok incoming) :
    let token := state.construction.exitReservations.size
    let waited := { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.push (.waiting incoming) } }
    waitExitDestination incoming state.construction = .ok token waited.construction ∧
      selectCompletionChannel source (.bytes ty bytes origin) (.completion token) waited =
        .ok (.construct incoming) { waited with construction := { waited.construction with
          exitReservations := waited.construction.exitReservations.set! token (.active .fresh incoming incoming snapshot) } } := by
  dsimp only
  constructor
  · simp [waitExitDestination, ConstructionM.get, ConstructionM.set, bind, pure]
  · apply selectCompletionChannel_open_byte_direct
    · simp
    · exact present
    · exact opened
    · simpa only [destinationCurrent_congr_tables state.construction
        { state.construction with exitReservations := state.construction.exitReservations.push (.waiting incoming) }
        rfl rfl incoming] using current

#print axioms completion_open_child_write_activates_ticket
#print axioms selectWaiting_open_child_direct
#print axioms selectCompletionChannel_open_byte_direct
#print axioms wait_then_select_completion_open_byte

end Goose.Proofs.ConstructionAcceptedExecution
