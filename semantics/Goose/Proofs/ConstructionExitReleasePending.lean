import Goose.Proofs.ConstructionExitReturnedWorld
import Goose.Proofs.ConstructionExitProtectionCleanup
import Goose.Proofs.ConstructionExitReceiverParent

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

def receivingCarrierReady_release_ticket (state : ExecutionState) (released incoming source : Nat)
    (ready : ReceivingCarrierLandingReady state incoming source) :
    ReceivingCarrierLandingReady { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! released .released } } incoming source := by
  have current := destinationCurrent_congr_tables state.construction
    { state.construction with exitReservations := state.construction.exitReservations.set! released .released } rfl rfl incoming
  have parent : LandingParentReady { state.construction with exitReservations := state.construction.exitReservations.set! released .released } ready.receiving ready.receivingDestination := by
    cases ready.parent with
    | receiver use => exact .receiver use
    | child parentId count parent use present progress => exact .child parentId count parent use present progress
    | replacement parentId count parent use present progress => exact .replacement parentId count parent use present progress
  exact ⟨ready.receiving, ready.sourceDestination, ready.receivingDestination,
    current.trans ready.resolved, ready.sourcePresent, ready.receivingPresent, ready.path, parent, ready.ordered⟩

theorem carriersReady_release_ticket (state : ExecutionState) (released : Nat) (channels : List Channel) (carriers : List Carrier)
    (ready : CarriersLandingReady state channels carriers) (separate : .completion released ∉ channels) :
    CarriersLandingReady { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! released .released } } channels carriers := by
  refine ⟨ready.lengths, ?_⟩
  intro channel carrier member
  have previous := ready.pairs channel carrier member
  cases previous with
  | register ty value => exact .register ty value
  | construct incoming source sourceReady => exact .construct incoming source (receivingCarrierReady_release_ticket state released incoming source sourceReady)
  | completion token incoming selected source role snapshot ticket sourceReady =>
    have channelMember : Channel.completion token ∈ channels := (List.of_mem_zip member).1
    have different : released ≠ token := by
      intro same
      subst token
      exact separate channelMember
    have unchanged : (state.construction.exitReservations.set! released .released)[token]? =
        state.construction.exitReservations[token]? := by
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, different]
    exact .completion token incoming selected source role snapshot (by simpa only [unchanged] using ticket)
      (receivingCarrierReady_release_ticket state released selected source sourceReady)
  | pendingNamed token incoming selected snapshot ticket =>
    have channelMember : Channel.completion token ∈ channels := (List.of_mem_zip member).1
    have different : released ≠ token := by
      intro same
      subst token
      exact separate channelMember
    have unchanged : (state.construction.exitReservations.set! released .released)[token]? =
        state.construction.exitReservations[token]? := by
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, different]
    exact .pendingNamed token incoming selected snapshot (by simpa only [unchanged] using ticket)

theorem actual_cleanup_pending_readiness (state : ExecutionState) (token incoming selected : Nat)
    (snapshot : PendingDestination) (origin : OriginId) (returned : List Carrier)
    (pending : List PendingCarrierFrame)
    (ticket : state.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot))
    (ready : ∀ frame ∈ pending, CarriersLandingReady state frame.channels frame.carriers)
    (separate : ∀ frame ∈ pending, .completion token ∉ frame.channels) :
    ∃ cleaned, exitChannelCleanupBorrowed origin [] [token] false returned state = .ok () cleaned ∧
      ∀ frame ∈ pending, CarriersLandingReady cleaned frame.channels frame.carriers := by
  let cleaned := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! token .released } }
  have released := releaseExitReservation_active state.construction token .fresh incoming selected snapshot ticket
  have cleanup : exitChannelCleanupBorrowed origin [] [token] false returned state = .ok () cleaned := by
    simp only [exitChannelCleanupBorrowed, Bool.false_eq_true, ↓reduceIte, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.forIn_cons, List.forIn_nil, liftConstruction, released, bind, pure]
    rfl
  exact ⟨cleaned, cleanup, fun frame member => carriersReady_release_ticket state token frame.channels frame.carriers
    (ready frame member) (separate frame member)⟩

#print axioms actual_cleanup_pending_readiness
#print axioms carriersReady_release_ticket

end Goose.Proofs.ConstructionAcceptedExecution
