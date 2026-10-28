import Goose.Proofs.ConstructionExitMultiFresh
import Goose.Proofs.ConstructionExitReleaseBacking

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

def FreshExitTickets (state : ExecutionState) (tokens : List Nat) : Prop :=
  ∀ token ∈ tokens, ∃ incoming selected snapshot,
    state.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot)

theorem release_fresh_pending_loop (layout : LayoutEnv) (origin : OriginId) (tokens : List Nat)
    (state : ExecutionState) (pending : List PendingCarrierFrame)
    (distinct : tokens.Nodup) (tickets : FreshExitTickets state tokens)
    (frames : ∀ frame ∈ pending, CarriersLandingReady state frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking layout state carrier)
    (separate : ∀ token ∈ tokens, ∀ frame ∈ pending, .completion token ∉ frame.channels) :
    ∃ after, ((forIn tokens PUnit.unit fun token _ => do
      liftConstruction origin (releaseExitReservation token)
      pure (.yield PUnit.unit)) : EvalM PUnit) state = .ok PUnit.unit after ∧
      ∀ frame ∈ pending, CarriersLandingReady after frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking layout after carrier := by
  induction tokens generalizing state with
  | nil => exact ⟨state, by simp [pure], frames⟩
  | cons token rest ih =>
    have notMember : token ∉ rest := (List.nodup_cons.mp distinct).1
    have tailDistinct : rest.Nodup := (List.nodup_cons.mp distinct).2
    obtain ⟨incoming, selected, snapshot, ticket⟩ := tickets token (by simp)
    let next := { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! token .released } }
    have release := releaseExitReservation_active state.construction token .fresh incoming selected snapshot ticket
    have nextFrames : ∀ frame ∈ pending, CarriersLandingReady next frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking layout next carrier := by
      intro frame member
      exact ⟨carriersReady_release_ticket state token frame.channels frame.carriers (frames frame member).1
          (separate token (by simp) frame member),
        fun carrier carried => carrierBacking_release_fresh_ticket layout state token incoming selected snapshot ticket carrier
          ((frames frame member).2 carrier carried)⟩
    have nextTickets : FreshExitTickets next rest := by
      intro other member
      obtain ⟨oldIncoming, oldSelected, oldSnapshot, found⟩ := tickets other (by simp [member])
      have different : token ≠ other := by intro equal; subst other; exact notMember member
      refine ⟨oldIncoming, oldSelected, oldSnapshot, ?_⟩
      simpa [next, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, different] using found
    have nextSeparate : ∀ other ∈ rest, ∀ frame ∈ pending, .completion other ∉ frame.channels := by
      intro other member frame kept
      exact separate other (by simp [member]) frame kept
    obtain ⟨after, loop, finalFrames⟩ := ih next tailDistinct nextTickets nextFrames nextSeparate
    refine ⟨after, ?_, finalFrames⟩
    simp only [List.forIn_cons, liftConstruction, release, bind, pure]
    exact loop

theorem actual_multi_exit_cleanup_pending (layout : LayoutEnv) (origin : OriginId) (tokens : List Nat)
    (state : ExecutionState) (carriers : List Carrier) (pending : List PendingCarrierFrame)
    (distinct : tokens.Nodup) (tickets : FreshExitTickets state tokens)
    (frames : ∀ frame ∈ pending, CarriersLandingReady state frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking layout state carrier)
    (separate : ∀ token ∈ tokens, ∀ frame ∈ pending, .completion token ∉ frame.channels) :
    ∃ after, exitChannelCleanupBorrowed origin [] tokens false carriers state = .ok () after ∧
      ∀ frame ∈ pending, CarriersLandingReady after frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking layout after carrier := by
  have reversedDistinct : tokens.reverse.Nodup := by
    apply List.pairwise_reverse.mpr
    simpa only [List.Nodup, ne_eq, eq_comm] using distinct
  have reversedTickets : FreshExitTickets state tokens.reverse := by simpa [FreshExitTickets] using tickets
  have reversedSeparate : ∀ token ∈ tokens.reverse, ∀ frame ∈ pending, .completion token ∉ frame.channels := by
    simpa using separate
  obtain ⟨after, loop, result⟩ := release_fresh_pending_loop layout origin tokens.reverse state pending
    reversedDistinct reversedTickets frames reversedSeparate
  refine ⟨after, ?_, result⟩
  simp only [bind, pure] at loop
  simp only [exitChannelCleanupBorrowed, Bool.false_eq_true, ↓reduceIte, bind, pure]
  rw [loop]

theorem exitChannelReservationTokens_distinct (first : Nat) (state : ExecutionState) :
    (exitChannelReservationTokens first state).Nodup := by
  unfold exitChannelReservationTokens
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp (l := List.range (state.construction.exitReservations.size - first)) _ List.nodup_range
  intro left right unequal same
  exact unequal (Nat.add_left_cancel same)

theorem actual_fresh_multi_cleanup_pending (config : EvalConfig) (initialized : Nat) (origin : OriginId)
    (before prepared state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (carriers : List Carrier)
    (oldWorld : AcceptedWorld config initialized before ambient types live regions pending)
    (tickets : FreshExitTickets state (exitChannelReservationTokens before.construction.exitReservations.size prepared))
    (frames : ∀ frame ∈ pending, CarriersLandingReady state frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout state carrier) :
    ∃ after, exitChannelCleanupBorrowed origin [] (exitChannelReservationTokens before.construction.exitReservations.size prepared)
      false carriers state = .ok () after ∧
      ∀ frame ∈ pending, CarriersLandingReady after frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout after carrier := by
  exact actual_multi_exit_cleanup_pending config.layout origin _ state carriers pending
    (exitChannelReservationTokens_distinct before.construction.exitReservations.size prepared) tickets frames
    (exitChannelReservationTokens_pending_separate config initialized before prepared ambient types live regions pending oldWorld)

#print axioms actual_fresh_multi_cleanup_pending
#print axioms exitChannelReservationTokens_distinct
#print axioms actual_multi_exit_cleanup_pending
#print axioms release_fresh_pending_loop

end Goose.Proofs.ConstructionAcceptedExecution
