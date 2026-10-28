import Goose.Proofs.ConstructionExitMultiCleanup
import Goose.Proofs.ConstructionExitRetainedCancellation

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

def RetainedFreshExitTickets (state : ExecutionState) (tokens : List Nat) (carried : List Nat) : Prop :=
  ∀ token ∈ tokens, ∃ incoming reserved selected snapshot,
    state.construction.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) ∧
    destinationCurrent state.construction reserved = .ok selected ∧
    carried.any (destinationDescendant state.construction.destinations selected) = true

theorem retained_fresh_cancel_loop (layout : LayoutEnv) (origin : OriginId) (tokens carried : List Nat)
    (state : ExecutionState) (pending : List PendingCarrierFrame)
    (distinct : tokens.Nodup) (tickets : RetainedFreshExitTickets state tokens carried)
    (frames : ∀ frame ∈ pending, CarriersLandingReady state frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking layout state carrier)
    (separate : ∀ token ∈ tokens, ∀ frame ∈ pending, .completion token ∉ frame.channels) :
    ∃ after, ((forIn tokens PUnit.unit fun token _ => do
      liftConstruction origin (cancelExitReservation token carried)
      liftConstruction origin (releaseExitReservation token)
      pure (.yield PUnit.unit)) : EvalM PUnit) state = .ok PUnit.unit after ∧
      ∀ frame ∈ pending, CarriersLandingReady after frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking layout after carrier := by
  induction tokens generalizing state with
  | nil => exact ⟨state, by simp [pure], frames⟩
  | cons token rest ih =>
    have notMember : token ∉ rest := (List.nodup_cons.mp distinct).1
    have tailDistinct : rest.Nodup := (List.nodup_cons.mp distinct).2
    obtain ⟨incoming, reserved, selected, snapshot, ticket, resolved, retained⟩ := tickets token (by simp)
    let next := { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! token .released } }
    have cancel := cancelExitReservation_retained_descendant state.construction token incoming reserved selected snapshot carried ticket resolved retained
    have release := releaseExitReservation_active state.construction token .fresh incoming reserved snapshot ticket
    have nextFrames : ∀ frame ∈ pending, CarriersLandingReady next frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking layout next carrier := by
      intro frame member
      exact ⟨carriersReady_release_ticket state token frame.channels frame.carriers (frames frame member).1
          (separate token (by simp) frame member),
        fun carrier carriedMember => carrierBacking_release_fresh_ticket layout state token incoming reserved snapshot ticket carrier
          ((frames frame member).2 carrier carriedMember)⟩
    have nextTickets : RetainedFreshExitTickets next rest carried := by
      intro other member
      obtain ⟨oldIncoming, oldReserved, oldSelected, oldSnapshot, found, current, covered⟩ := tickets other (by simp [member])
      have different : token ≠ other := by intro equal; subst other; exact notMember member
      refine ⟨oldIncoming, oldReserved, oldSelected, oldSnapshot, ?_, ?_, covered⟩
      · simpa [next, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, different] using found
      · have same := destinationCurrent_congr_tables state.construction next.construction rfl rfl oldReserved
        exact same.trans current
    have nextSeparate : ∀ other ∈ rest, ∀ frame ∈ pending, .completion other ∉ frame.channels := by
      intro other member frame kept
      exact separate other (by simp [member]) frame kept
    obtain ⟨after, loop, finalFrames⟩ := ih next tailDistinct nextTickets nextFrames nextSeparate
    refine ⟨after, ?_, finalFrames⟩
    simp only [List.forIn_cons, liftConstruction, cancel, release, bind, pure]
    exact loop

theorem actual_retained_multi_cancel_pending (layout : LayoutEnv) (origin : OriginId) (tokens : List Nat)
    (state : ExecutionState) (carriers : List Carrier) (pending : List PendingCarrierFrame)
    (distinct : tokens.Nodup)
    (tickets : RetainedFreshExitTickets state tokens (carriers.filterMap fun carrier =>
      match carrier with | Carrier.completed id => some id | _ => none))
    (frames : ∀ frame ∈ pending, CarriersLandingReady state frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking layout state carrier)
    (separate : ∀ token ∈ tokens, ∀ frame ∈ pending, .completion token ∉ frame.channels) :
    ∃ after, exitChannelCleanupBorrowed origin [] tokens true carriers state = .ok () after ∧
      ∀ frame ∈ pending, CarriersLandingReady after frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking layout after carrier := by
  have reversedDistinct : tokens.reverse.Nodup := by
    apply List.pairwise_reverse.mpr
    simpa only [List.Nodup, ne_eq, eq_comm] using distinct
  have reversedTickets : RetainedFreshExitTickets state tokens.reverse (carriers.filterMap fun carrier =>
      match carrier with | Carrier.completed id => some id | _ => none) := by simpa [RetainedFreshExitTickets] using tickets
  have reversedSeparate : ∀ token ∈ tokens.reverse, ∀ frame ∈ pending, .completion token ∉ frame.channels := by simpa using separate
  obtain ⟨after, loop, result⟩ := retained_fresh_cancel_loop layout origin tokens.reverse _ state pending
    reversedDistinct reversedTickets frames reversedSeparate
  refine ⟨after, ?_, result⟩
  change (do
    let _ ← ((forIn tokens.reverse PUnit.unit fun token _ => do
      liftConstruction origin (cancelExitReservation token (carriers.filterMap fun carrier =>
        match carrier with | Carrier.completed id => some id | _ => none))
      liftConstruction origin (releaseExitReservation token)
      pure (.yield PUnit.unit)) : EvalM PUnit)
    pure ()) state = .ok () after
  simp only [bind, pure] at loop ⊢
  rw [loop]

theorem actual_fresh_multi_cancel_pending (config : EvalConfig) (initialized : Nat) (origin : OriginId)
    (before prepared state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (carriers : List Carrier)
    (oldWorld : AcceptedWorld config initialized before ambient types live regions pending)
    (tickets : RetainedFreshExitTickets state (exitChannelReservationTokens before.construction.exitReservations.size prepared)
      (carriers.filterMap fun carrier => match carrier with | Carrier.completed id => some id | _ => none))
    (frames : ∀ frame ∈ pending, CarriersLandingReady state frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout state carrier) :
    ∃ after, exitChannelCleanupBorrowed origin [] (exitChannelReservationTokens before.construction.exitReservations.size prepared)
      true carriers state = .ok () after ∧
      ∀ frame ∈ pending, CarriersLandingReady after frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout after carrier := by
  exact actual_retained_multi_cancel_pending config.layout origin _ state carriers pending
    (exitChannelReservationTokens_distinct before.construction.exitReservations.size prepared) tickets frames
    (exitChannelReservationTokens_pending_separate config initialized before prepared ambient types live regions pending oldWorld)

#print axioms actual_fresh_multi_cancel_pending
#print axioms actual_retained_multi_cancel_pending
#print axioms retained_fresh_cancel_loop

end Goose.Proofs.ConstructionAcceptedExecution
