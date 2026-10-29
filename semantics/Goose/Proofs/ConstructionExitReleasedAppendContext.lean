import Goose.Proofs.ConstructionExitWaitingReleaseSource

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct
open Goose.Proofs.ConstructionAcceptedExecution
open Goose.Proofs.ConstructionExecutionProtocol

theorem released_ticket_append_context (before : ExecutionState) (ambient : OwnershipAmbient)
    (valid : OwnershipExecutionContext before ambient)
    (history : ReservationReferencesBounded before.construction ambient) :
    OwnershipExecutionContext { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push .released } } ambient := by
  let token := before.construction.exitReservations.size
  let waited := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push (.waiting 0) } }
  let after := { waited with construction := { waited.construction with
    exitReservations := waited.construction.exitReservations.set! token .released } }
  have context := waitExitDestination_context before 0 ambient valid history
  have waiting : waited.construction.exitReservations[token]? = some (.waiting 0) := by simp [waited, token]
  have source := ownershipSource_after_waiting_release waited.construction token 0 waiting context.source
  have captures := captured_receiving_after_release waited.construction token ambient context.bounds.2 context.receiving.2
  have anchors := retained_anchors_after_release waited.construction token ambient.retained (by
    simpa [OwnershipAmbient.retained, OwnershipAmbientFrame.carriers] using context.retention.anchors)
  have boundaries := retained_boundaries_after_release waited.construction token ambient context.retention.boundaries.2
  have reservations : OwnershipReservationFrames after.construction ambient := by
    intro other reservation present needed
    have released : after.construction.exitReservations[token]? = some .released := by
      simp [after, waited, token, Array.set!_eq_setIfInBounds, Array.setIfInBounds, Array.set_push]
    by_cases same : other = token
    · subst other
      have equal : reservation = .released := Option.some.inj (present.symm.trans released)
      subst reservation
      exact False.elim needed
    · have old : before.construction.exitReservations[other]? = some reservation := by
        simpa [after, waited, token, Array.set!_eq_setIfInBounds, Array.setIfInBounds, Array.set_push,
          Array.getElem?_push, same] using present
      exact valid.reservations other reservation old needed
  have afterContext : OwnershipExecutionContext after ambient := by
    refine ⟨source, ⟨source.structural.1, anchors, boundaries⟩, ?_, reservations, captures.2, captures.1, ?_⟩
    · exact ⟨valid.runtime.activations, valid.runtime.breaks⟩
    · exact ⟨valid.identities.activations, valid.identities.breaks⟩
  have exactState : after = { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push .released } } := by
    simp [after, waited, token, Array.set!_eq_setIfInBounds, Array.setIfInBounds, Array.set_push]
  simpa only [exactState] using afterContext

#print axioms released_ticket_append_context

end Goose.Proofs.ConstructionExecutionOwnership
