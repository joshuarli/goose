import Goose.Proofs.ConstructionExitCompletionReservation
import Goose.Proofs.ConstructionExitChildWrite

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem completion_write_excludes_active_sibling (state : ExecutionState) (source : RuntimeActivation)
    (completion incoming parentId parentCount : Nat) (snapshot parent : PendingDestination)
    (ty : Goose.Construct.Ty) (bytes : List UInt8) (origin : OriginId) (payload : ByteArray)
    (waiting : state.construction.exitReservations[completion]? = some (.waiting incoming))
    (present : state.construction.destinations[incoming]? = some snapshot) (opened : snapshot.progress = .open 0)
    (current : destinationCurrent state.construction incoming = .ok incoming)
    (childUse : snapshot.use = .child parentId)
    (parentFound : state.construction.destinations[parentId]? = some parent)
    (parentPhase : parent.progress = .suspended parentCount incoming)
    (lifecycle : ReservationLifecycleInvariant state.construction)
    (unique : ActiveChildUnique state.construction) (blocked : ActiveChildParentBlocked state.construction)
    (written : ConstructionState)
    (write : writeElement incoming payload { state.construction with
      exitReservations := state.construction.exitReservations.set! completion (.active .fresh incoming incoming snapshot) } = .ok () written) :
    ∃ activated,
      selectCompletionChannel source (.bytes ty bytes origin) (.completion completion) state = .ok (.construct incoming) activated ∧
      written.exitReservations[completion]? = some (.active .fresh incoming incoming snapshot) ∧
      written.destinations[parentId]? = some parent ∧
      ∀ sibling row, written.destinations[sibling]? = some row → row.use = .child parentId →
        activeRow row = true → sibling = incoming := by
  let activated := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! completion (.active .fresh incoming incoming snapshot) } }
  have activatedUnique : ActiveChildUnique activated.construction := by
    simpa only [ActiveChildUnique, activated] using unique
  have activatedBlocked : ActiveChildParentBlocked activated.construction := by
    simpa only [ActiveChildParentBlocked, activated] using blocked
  have invariant := writeElement_preserves_child_invariants activated.construction written incoming payload activatedUnique activatedBlocked write
  obtain ⟨actual, selection, ticket, parentAfter, _, childAfter⟩ :=
    completion_open_child_write_activates_ticket state source completion incoming parentId parentCount snapshot parent ty bytes origin payload
      waiting present opened current childUse parentFound parentPhase lifecycle written write
  refine ⟨actual, selection, ticket, parentAfter, ?_⟩
  intro sibling row found use active
  exact invariant.1 parentId sibling incoming row
    { snapshot with progress := .open 1, writeEnd := snapshot.writeEnd + payload.size }
    found use active childAfter childUse (by simp [activeRow])

#print axioms completion_write_excludes_active_sibling

end Goose.Proofs.ConstructionAcceptedExecution
