import Goose.Proofs.ConstructionExitMultiRetainedCleanup
import Goose.Proofs.ConstructionExitNamedCleanup

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

def CancelableExitTicket (state : ExecutionState) (token : Nat) (carried : List Nat) : Prop :=
  (∃ incoming reserved selected snapshot,
    state.construction.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) ∧
    destinationCurrent state.construction reserved = .ok selected ∧
    carried.any (destinationDescendant state.construction.destinations selected) = true) ∨
  ∃ stage incoming selected snapshot,
    state.construction.exitReservations[token]? = some (.active (.named stage) incoming selected snapshot)

theorem liftConstruction_sequence (origin : OriginId) (first : ConstructionM Unit) (second : ConstructionM Unit)
    (state : ExecutionState) :
    (do liftConstruction origin first; liftConstruction origin second) state =
      liftConstruction origin (do first; second) state := by
  simp only [bind, liftConstruction]
  cases result : first state.construction <;> rfl

theorem cancelable_ticket_step (layout : LayoutEnv) (origin : OriginId) (token : Nat)
    (state : ExecutionState) (carried : List Nat) (pending : List PendingCarrierFrame)
    (ticket : CancelableExitTicket state token carried)
    (frames : ∀ frame ∈ pending, CarriersLandingReady state frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking layout state carrier)
    (separate : ∀ frame ∈ pending, .completion token ∉ frame.channels) :
    let next := { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! token .released } }
    (do
      liftConstruction origin (cancelExitReservation token carried)
      liftConstruction origin (releaseExitReservation token)) state = .ok () next ∧
    ∀ frame ∈ pending, CarriersLandingReady next frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking layout next carrier := by
  let next := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! token .released } }
  have transition : (do cancelExitReservation token carried; releaseExitReservation token) state.construction = .ok () next.construction := by
    rcases ticket with fresh | named
    · obtain ⟨incoming, reserved, selected, snapshot, found, current, retained⟩ := fresh
      have cancel := cancelExitReservation_retained_descendant state.construction token incoming reserved selected snapshot carried found current retained
      have release := releaseExitReservation_active state.construction token .fresh incoming reserved snapshot found
      simp only [bind, cancel, release]
      rfl
    · obtain ⟨stage, incoming, selected, snapshot, found⟩ := named
      exact named_ticket_cancel_release state.construction token incoming selected stage snapshot carried found
  refine ⟨?_, ?_⟩
  · rw [liftConstruction_sequence]
    simp only [liftConstruction, transition]
    rfl
  · intro frame member
    have ready := (frames frame member).1
    refine ⟨carriersReady_release_ticket state token frame.channels frame.carriers ready (separate frame member), ?_⟩
    intro carrier carriedMember
    have different : carrier ≠ .pendingNamed token := by
      intro same
      subst carrier
      exact separate frame member (ready_pendingNamed_channel state frame.channels frame.carriers ready token carriedMember)
    exact carrierBacking_release_other_ticket layout state token carrier ((frames frame member).2 carrier carriedMember) different

theorem cancelable_ticket_after_release (state : ExecutionState) (released token : Nat) (carried : List Nat)
    (different : released ≠ token) (ticket : CancelableExitTicket state token carried) :
    CancelableExitTicket { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! released .released } } token carried := by
  have unchanged : (state.construction.exitReservations.set! released .released)[token]? = state.construction.exitReservations[token]? := by
    simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, different]
  rcases ticket with fresh | named
  · obtain ⟨incoming, reserved, selected, snapshot, found, current, retained⟩ := fresh
    left
    refine ⟨incoming, reserved, selected, snapshot, ?_, ?_, retained⟩
    · simpa only [unchanged] using found
    · exact (destinationCurrent_congr_tables state.construction
      { state.construction with exitReservations := state.construction.exitReservations.set! released .released } rfl rfl reserved).trans current
  · obtain ⟨stage, incoming, selected, snapshot, found⟩ := named
    exact Or.inr ⟨stage, incoming, selected, snapshot, by simpa only [unchanged] using found⟩

theorem mixed_cancel_loop (layout : LayoutEnv) (origin : OriginId) (tokens carried : List Nat)
    (state : ExecutionState) (pending : List PendingCarrierFrame)
    (distinct : tokens.Nodup) (tickets : ∀ token ∈ tokens, CancelableExitTicket state token carried)
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
    let next := { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! token .released } }
    have step := cancelable_ticket_step layout origin token state carried pending (tickets token (by simp)) frames
      (fun frame member => separate token (by simp) frame member)
    have nextTickets : ∀ other ∈ rest, CancelableExitTicket next other carried := by
      intro other member
      have different : token ≠ other := by intro equal; subst other; exact notMember member
      exact cancelable_ticket_after_release state token other carried different (tickets other (by simp [member]))
    have nextSeparate : ∀ other ∈ rest, ∀ frame ∈ pending, .completion other ∉ frame.channels := by
      intro other member frame kept
      exact separate other (by simp [member]) frame kept
    obtain ⟨after, loop, finalFrames⟩ := ih next tailDistinct nextTickets step.2 nextSeparate
    refine ⟨after, ?_, finalFrames⟩
    simp only [List.forIn_cons]
    have sequence := step.1
    simp only [bind] at sequence loop ⊢
    cases cancelled : liftConstruction origin (cancelExitReservation token carried) state with
    | stop reason stopped => simp only [cancelled] at sequence; cases sequence
    | escape address carriers escaped => simp only [cancelled] at sequence; cases sequence
    | jump target kind jumped => simp only [cancelled] at sequence; cases sequence
    | ok value middle =>
      simp only [cancelled] at sequence ⊢
      rw [sequence]
      simpa only [pure] using loop

theorem actual_mixed_cancel_pending (layout : LayoutEnv) (origin : OriginId) (tokens : List Nat)
    (state : ExecutionState) (carriers : List Carrier) (pending : List PendingCarrierFrame)
    (distinct : tokens.Nodup)
    (tickets : ∀ token ∈ tokens, CancelableExitTicket state token (carriers.filterMap fun carrier =>
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
  have reversedTickets : ∀ token ∈ tokens.reverse, CancelableExitTicket state token (carriers.filterMap fun carrier =>
      match carrier with | Carrier.completed id => some id | _ => none) := by simpa using tickets
  have reversedSeparate : ∀ token ∈ tokens.reverse, ∀ frame ∈ pending, .completion token ∉ frame.channels := by simpa using separate
  obtain ⟨after, loop, result⟩ := mixed_cancel_loop layout origin tokens.reverse _ state pending
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

theorem actual_exit_mixed_cancel_pending (config : EvalConfig) (initialized : Nat) (origin : OriginId)
    (before prepared state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (carriers : List Carrier)
    (oldWorld : AcceptedWorld config initialized before ambient types live regions pending)
    (tickets : ∀ token ∈ exitChannelReservationTokens before.construction.exitReservations.size prepared,
      CancelableExitTicket state token (carriers.filterMap fun carrier =>
        match carrier with | Carrier.completed id => some id | _ => none))
    (frames : ∀ frame ∈ pending, CarriersLandingReady state frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout state carrier) :
    ∃ after, exitChannelCleanupBorrowed origin [] (exitChannelReservationTokens before.construction.exitReservations.size prepared)
      true carriers state = .ok () after ∧
      ∀ frame ∈ pending, CarriersLandingReady after frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout after carrier := by
  exact actual_mixed_cancel_pending config.layout origin _ state carriers pending
    (exitChannelReservationTokens_distinct before.construction.exitReservations.size prepared) tickets frames
    (exitChannelReservationTokens_pending_separate config initialized before prepared ambient types live regions pending oldWorld)

#print axioms actual_exit_mixed_cancel_pending
#print axioms actual_mixed_cancel_pending
#print axioms mixed_cancel_loop
#print axioms cancelable_ticket_step
#print axioms liftConstruction_sequence

end Goose.Proofs.ConstructionAcceptedExecution
