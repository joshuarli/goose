import Goose.Proofs.ConstructionExitFrameRelease
import Goose.Proofs.OwnershipRuntimeIdentities

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct

theorem cleanup_exit_frame_runtime_unwind (state : ExecutionState) (token incoming selected : Nat)
    (snapshot : PendingDestination) (channels : List Channel) (carriers : List Carrier)
    (outer : OwnershipAmbient) (origin : Goose.Core.OriginId)
    (environment : RuntimeActivation) (scope : Nat) (scopeInst : Goose.Core.ScopeInst)
    (ticket : state.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot))
    (frames : OwnershipReservationFrames state.construction (.exitChannels [token] channels carriers :: outer))
    (runtime : OwnershipRuntimeFrames state (.exitChannels [token] channels carriers :: outer))
    (identities : OwnershipRuntimeIdentities state) :
    ∃ cleaned,
      Goose.Proofs.ExitExecution.exitChannelCleanupBorrowed origin [] [token] false carriers state = .ok () cleaned ∧
      OwnershipReservationFrames (releaseScopeState environment scope scopeInst cleaned).construction outer ∧
      OwnershipRuntimeFrames (releaseScopeState environment scope scopeInst cleaned) outer ∧
      OwnershipRuntimeIdentities (releaseScopeState environment scope scopeInst cleaned) := by
  obtain ⟨cleaned, cleanup, discharged, remaining⟩ :=
    cleanup_single_exit_frame state token incoming selected snapshot channels carriers outer origin ticket frames
  have released := releaseExitReservation_active state.construction token .fresh incoming selected snapshot ticket
  have exactCleanup : Goose.Proofs.ExitExecution.exitChannelCleanupBorrowed origin [] [token] false carriers state =
      .ok () { state with construction := { state.construction with
        exitReservations := state.construction.exitReservations.set! token .released } } := by
    simp only [Goose.Proofs.ExitExecution.exitChannelCleanupBorrowed, Bool.false_eq_true, ↓reduceIte,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.forIn_cons, List.forIn_nil,
      liftConstruction, released, bind, pure]
  have equal := cleanup.symm.trans exactCleanup
  cases equal
  have outerRuntime : OwnershipRuntimeFrames state outer := by
    exact ⟨by simpa [OwnershipAmbient.activations, OwnershipAmbientFrame.activationChannels, List.filterMap_cons] using runtime.activations,
      by simpa [OwnershipAmbient.breaks, OwnershipAmbientFrame.breakChannels, List.filterMap_cons] using runtime.breaks⟩
  have cleanRuntime : OwnershipRuntimeFrames { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! token .released } } outer := ⟨outerRuntime.activations, outerRuntime.breaks⟩
  have cleanIdentities : OwnershipRuntimeIdentities { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! token .released } } := ⟨identities.activations, identities.breaks⟩
  exact ⟨_, exactCleanup, remaining, ownershipRuntimeFrames_releaseScope environment scope scopeInst _ outer cleanRuntime,
    ownershipRuntimeIdentities_releaseScope cleanIdentities environment scope scopeInst⟩

#print axioms cleanup_exit_frame_runtime_unwind

end Goose.Proofs.ConstructionExecutionOwnership
