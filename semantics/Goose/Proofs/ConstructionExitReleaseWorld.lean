import Goose.Proofs.ConstructionExitReleaseBacking
import Goose.Proofs.ConstructionExitStructuralRelease

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem exit_cleanup_context (state : ExecutionState) (token incoming selected : Nat)
    (snapshot : PendingDestination) (channels : List Channel) (carriers : List Carrier)
    (outer : OwnershipAmbient)
    (ticket : state.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot))
    (context : OwnershipExecutionContext state (.exitChannels [token] channels carriers :: outer)) :
    OwnershipExecutionContext { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! token .released } } (.returned carriers :: outer) := by
  let final := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! token .released } }
  have source := ownershipSource_after_ticket_release state.construction token incoming selected snapshot ticket context.source
  have retention := exit_retention_after_release state.construction token channels carriers outer context.retention
  have captured := captured_receiving_after_release state.construction token outer context.bounds.2 context.receiving.2
  obtain ⟨other, released, _, frames⟩ := release_single_exit_frame state.construction token incoming selected snapshot channels carriers outer ticket context.reservations
  have actual := releaseExitReservation_active state.construction token .fresh incoming selected snapshot ticket
  have same := released.symm.trans actual
  cases same
  have runtime : OwnershipRuntimeFrames final outer := ⟨by simpa [OwnershipAmbient.activations, OwnershipAmbientFrame.activationChannels, List.filterMap_cons] using context.runtime.activations,
    by simpa [OwnershipAmbient.breaks, OwnershipAmbientFrame.breakChannels, List.filterMap_cons] using context.runtime.breaks⟩
  refine ⟨source, ⟨source.structural.1, retention.1, retention.2⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ownershipRuntimeFrames_returned final outer carriers).mpr runtime
  · exact (ownershipReservationFrames_returned final.construction outer carriers).mpr frames
  · exact (ownershipCapturedReceivingFrames_returned final.construction outer carriers).mpr captured.2
  · exact (ownershipCapturedReceivingBounds_returned final.construction outer carriers).mpr captured.1
  · exact ⟨context.identities.activations, context.identities.breaks⟩

theorem exit_cleanup_accepted_world (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (token incoming selected : Nat) (snapshot : PendingDestination) (channels : List Channel) (carriers : List Carrier)
    (outer : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame) (origin : OriginId)
    (ticket : state.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot))
    (world : AcceptedWorld config initialized state (.exitChannels [token] channels carriers :: outer) types live regions pending)
    (separate : ∀ frame ∈ pending, .completion token ∉ frame.channels) :
    ∃ cleaned, exitChannelCleanupBorrowed origin [] [token] false carriers state = .ok () cleaned ∧
      AcceptedWorld config initialized cleaned (.returned carriers :: outer) types live regions pending := by
  obtain ⟨cleaned, cleanup, frames⟩ := actual_cleanup_pending_frames config.layout state token incoming selected snapshot origin carriers pending ticket world.carriers separate
  let final := { state with construction := { state.construction with exitReservations := state.construction.exitReservations.set! token .released } }
  have released := releaseExitReservation_active state.construction token .fresh incoming selected snapshot ticket
  have actual : exitChannelCleanupBorrowed origin [] [token] false carriers state = .ok () final := by
    simp only [exitChannelCleanupBorrowed, Bool.false_eq_true, ↓reduceIte, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.forIn_cons, List.forIn_nil, liftConstruction, released, bind, pure]
    rfl
  have same : cleaned = final := (ExecutionStep.ok.inj (cleanup.symm.trans actual)).2
  rw [same] at frames
  refine ⟨final, actual, ⟨⟨exit_cleanup_context state token incoming selected snapshot channels carriers outer ticket world.ownership,
    world.globals, world.globalTypes, world.layouts, world.typeFrontier, world.syntheticFrontier, world.heap,
    world.objectsRegistered, world.ordinalsRegistered, ?_, ?_, frames⟩, world.globalLive⟩⟩
  · constructor
    · intro root retained value found
      exact valueBacking_release_ticket config.layout state token value (world.backing.values root retained value found)
    · exact world.backing.identities
  · intro region member
    exact receivingProtection_release_ticket config.layout state live region token (world.protections region member)

theorem exit_cleanup_returned_world (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (token incoming selected : Nat) (snapshot : PendingDestination) (channels targetChannels : List Channel) (carriers : List Carrier)
    (outer : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame) (origin : OriginId)
    (ticket : state.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot))
    (world : AcceptedWorld config initialized state (.exitChannels [token] channels carriers :: outer) types live regions pending)
    (separate : ∀ frame ∈ pending, .completion token ∉ frame.channels)
    (targetSeparate : .completion token ∉ targetChannels)
    (targetReady : CarriersLandingReady state targetChannels carriers)
    (targetBacked : ∀ carrier ∈ carriers, CarrierResultBacking config.layout state carrier) :
    ∃ cleaned, exitChannelCleanupBorrowed origin [] [token] false carriers state = .ok () cleaned ∧
      AcceptedWorld config initialized cleaned (.returned carriers :: outer) types live regions
        (⟨targetChannels, carriers⟩ :: pending) := by
  have augmented : AcceptedWorld config initialized state (.exitChannels [token] channels carriers :: outer) types live regions
      (⟨targetChannels, carriers⟩ :: pending) := by
    refine ⟨{ world.toAcceptedWorldCore with carriers := ?_ }, world.globalLive⟩
    intro frame member
    rcases List.mem_cons.mp member with same | old
    · subst frame
      exact ⟨targetReady, targetBacked⟩
    · exact world.carriers frame old
  apply exit_cleanup_accepted_world config initialized state token incoming selected snapshot channels carriers outer types live regions
    (⟨targetChannels, carriers⟩ :: pending) origin ticket augmented
  intro frame member
  rcases List.mem_cons.mp member with same | old
  · subst frame
    exact targetSeparate
  · exact separate frame old

#print axioms exit_cleanup_returned_world
#print axioms exit_cleanup_context
#print axioms exit_cleanup_accepted_world

end Goose.Proofs.ConstructionAcceptedExecution
