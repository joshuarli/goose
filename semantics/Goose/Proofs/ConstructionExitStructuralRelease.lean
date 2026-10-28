import Goose.Proofs.ConstructionExitSourceRelease
import Goose.Proofs.ConstructionExitRuntimeUnwind

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct
open Goose.Proofs.ConstructionExecutionProtocol

theorem ownershipSource_after_ticket_release (state : ConstructionState) (token : Nat)
    (incoming selected : Nat) (snapshot : PendingDestination)
    (present : state.exitReservations[token]? = some (.active .fresh incoming selected snapshot))
    (valid : OwnershipSourceState state) :
    OwnershipSourceState { state with exitReservations := state.exitReservations.set! token .released } := by
  let after := { state with exitReservations := state.exitReservations.set! token .released }
  have released := releaseExitReservation_active state token .fresh incoming selected snapshot present
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

theorem cleanup_exit_execution_context (state : ExecutionState) (token incoming selected : Nat)
    (snapshot : PendingDestination) (channels : List Channel) (carriers : List Carrier)
    (outer : OwnershipAmbient) (origin : Goose.Core.OriginId)
    (environment : RuntimeActivation) (scope : Nat) (scopeInst : Goose.Core.ScopeInst)
    (ticket : state.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot))
    (context : OwnershipExecutionContext state (.exitChannels [token] channels carriers :: outer)) :
    ∃ cleaned,
      Goose.Proofs.ExitExecution.exitChannelCleanupBorrowed origin [] [token] false carriers state = .ok () cleaned ∧
      OwnershipExecutionContext (releaseScopeState environment scope scopeInst cleaned) (.returned carriers :: outer) := by
  obtain ⟨cleaned, cleanup, capturedBounds, capturedFrames, reservationFrames⟩ :=
    cleanup_captured_receiving_outer state token incoming selected snapshot channels carriers outer origin environment scope scopeInst
      ticket context.bounds context.receiving context.reservations
  obtain ⟨other, otherCleanup, _, runtime, identities⟩ :=
    cleanup_exit_frame_runtime_unwind state token incoming selected snapshot channels carriers outer origin environment scope scopeInst
      ticket context.reservations context.runtime context.identities
  have same := cleanup.symm.trans otherCleanup
  cases same
  obtain ⟨third, thirdCleanup, anchors, boundaries⟩ :=
    exit_retention_cleanup state token incoming selected snapshot channels carriers outer origin ticket context.retention
  have same := cleanup.symm.trans thirdCleanup
  cases same
  have released := releaseExitReservation_active state.construction token .fresh incoming selected snapshot ticket
  have actual : Goose.Proofs.ExitExecution.exitChannelCleanupBorrowed origin [] [token] false carriers state =
      .ok () { state with construction := { state.construction with
        exitReservations := state.construction.exitReservations.set! token .released } } := by
    simp only [Goose.Proofs.ExitExecution.exitChannelCleanupBorrowed, Bool.false_eq_true, ↓reduceIte,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.forIn_cons, List.forIn_nil,
      liftConstruction, released, bind, pure]
  have same := cleanup.symm.trans actual
  cases same
  have source := ownershipSource_after_ticket_release state.construction token incoming selected snapshot ticket context.source
  let final := releaseScopeState environment scope scopeInst
    { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! token .released } }
  refine ⟨_, actual, ⟨source, ⟨source.structural.1, anchors, boundaries⟩, ?_, ?_, ?_, ?_, identities⟩⟩
  · exact (ownershipRuntimeFrames_returned final outer carriers).mpr runtime
  · exact (ownershipReservationFrames_returned final.construction outer carriers).mpr reservationFrames
  · exact (ownershipCapturedReceivingFrames_returned final.construction outer carriers).mpr capturedFrames
  · exact (ownershipCapturedReceivingBounds_returned final.construction outer carriers).mpr capturedBounds

#print axioms cleanup_exit_execution_context
#print axioms ownershipSource_after_ticket_release

end Goose.Proofs.ConstructionExecutionOwnership
