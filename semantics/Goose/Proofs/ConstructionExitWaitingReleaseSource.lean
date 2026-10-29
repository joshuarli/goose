import Goose.Proofs.ConstructionExitStructuralRelease
import Goose.Proofs.ConstructionExitWaitingSource

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct
open Goose.Proofs.ConstructionExecutionProtocol

theorem ownershipSource_after_waiting_release (state : ConstructionState) (token : Nat)
    (incoming : Nat)
    (present : state.exitReservations[token]? = some (.waiting incoming))
    (valid : OwnershipSourceState state) :
    OwnershipSourceState { state with exitReservations := state.exitReservations.set! token .released } := by
  let after := { state with exitReservations := state.exitReservations.set! token .released }
  have released := releaseExitReservation_waiting state token incoming present
  have lifecycle := releaseExitReservation_lifecycle state token valid.structural.1.1
  rw [released] at lifecycle
  have roles := release_source_successor_roles state token valid
  have links : ConstructionOwnershipLinks after := by
    refine ⟨lifecycle.1, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · exact valid.structural.1.2.1.2.1
    · intro index incoming selected snapshot ticket
      exact valid.structural.1.2.1.2.2.1.1 index incoming selected snapshot
        (fresh_ticket_preimage state token index incoming selected snapshot ticket)
    · exact valid.structural.1.2.1.2.2.1.2
    · intro index incoming selected snapshot ticket
      exact valid.structural.1.2.1.2.2.2.1 index incoming selected snapshot
        (fresh_ticket_preimage state token index incoming selected snapshot ticket)
    · intro index incoming selected snapshot current ticket
      exact valid.structural.1.2.1.2.2.2.2.1 index incoming selected snapshot current
        (fresh_ticket_preimage state token index incoming selected snapshot ticket)
    · intro index incoming selected snapshot ticket
      exact valid.structural.1.2.1.2.2.2.2.2.1 index incoming selected snapshot
        (fresh_ticket_preimage state token index incoming selected snapshot ticket)
    · exact valid.structural.1.2.1.2.2.2.2.2.2
  have authority : SupportedReplacementAuthority after := by
    intro id parent row found use supported
    exact valid.structural.1.2.2.1 id parent row found use (replacementSupported_ticket_release state token id supported)
  have backing : ResumptionBackingSources after := valid.structural.1.2.2.2.1
  have unsupported : UnsupportedResumptionKeys after := by
    intro id saved found supported
    exact valid.structural.1.2.2.2.2.1 id saved found (replacementSupported_ticket_release state token id supported)
  have currentRoles : LiveFreshReservationRoles after := liveFreshReservationSuccessorRoles_current after roles.1
  have rawRoles : LiveFreshReservationRawRoles after := liveFreshReservationSuccessorRoles_raw after roles.1
  exact ⟨⟨⟨lifecycle, links, authority, backing, unsupported, currentRoles⟩, valid.structural.2.1, rawRoles⟩,
    roles.1, roles.2.1, roles.2.2⟩

#print axioms ownershipSource_after_waiting_release

end Goose.Proofs.ConstructionExecutionOwnership
