import Goose.Proofs.ConstructionExitReleasePending

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem storedBacking_release_ticket (layout : LayoutEnv) (state : ExecutionState) (released : Nat)
    (stored : StoredValue) (backed : StoredValueBacking layout state stored) :
    StoredValueBacking layout { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! released .released } } stored := by
  cases backed with
  | detached storage element present detached ty interval => exact .detached storage element present detached ty interval
  | named id storage destination count present named binding backing ty start progress element elementType interval =>
    exact .named id storage destination count present named binding backing ty start progress element elementType interval

theorem valueBacking_release_ticket (layout : LayoutEnv) (state : ExecutionState) (released : Nat)
    (value : Value) (backed : ValueStorageBacked layout state value) :
    ValueStorageBacked layout { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! released .released } } value := by
  induction backed with
  | integer ty value => exact .integer ty value
  | boolean value => exact .boolean value
  | unit => exact .unit
  | reference location => exact .reference location
  | slice location start count => exact .slice location start count
  | array values children ih => exact .array values ih
  | record id values children ih => exact .record id values ih
  | stored value backed => exact .stored value (storedBacking_release_ticket layout state released value backed)

theorem carrierBacking_release_fresh_ticket (layout : LayoutEnv) (state : ExecutionState)
    (released incoming selected : Nat) (snapshot : PendingDestination)
    (ticket : state.construction.exitReservations[released]? = some (.active .fresh incoming selected snapshot))
    (carrier : Carrier) (backed : CarrierResultBacking layout state carrier) :
    CarrierResultBacking layout { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! released .released } } carrier := by
  cases backed with
  | register value backing => exact .register value (valueBacking_release_ticket layout state released value backing)
  | completed id count destination stored present built sampled backing =>
    exact completed_carrier_after_ticket_release layout state released id (.completed id count destination stored present built sampled backing)
  | pendingNamed token oldIncoming oldSelected count oldSnapshot source stored named present marked phase sampled backing =>
    have different : released ≠ token := by
      intro same
      subst token
      cases ticket.symm.trans named
    have unchanged : (state.construction.exitReservations.set! released .released)[token]? = state.construction.exitReservations[token]? := by
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, different]
    have sampled' : storedDestination oldSelected { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! released .released } } = .ok stored
        { state with construction := { state.construction with exitReservations := state.construction.exitReservations.set! released .released } } := by
      simp only [storedDestination, getDestination, EvalM.get, bind, pure] at sampled ⊢
      cases found : state.construction.destinations[oldSelected]? with
      | none => simp [found, fault, EvalM.stop] at sampled
      | some row =>
        simp only [found] at sampled ⊢
        cases progress : progressCount row.progress with
        | none => simp [progress, fault, EvalM.stop] at sampled
        | some n => simp only [progress, ExecutionStep.ok.injEq] at sampled ⊢; exact sampled
    exact .pendingNamed token oldIncoming oldSelected count oldSnapshot source stored
      (by simpa only [unchanged] using named) present marked phase sampled' (storedBacking_release_ticket layout state released stored backing)

theorem actual_cleanup_pending_backing (layout : LayoutEnv) (state : ExecutionState)
    (token incoming selected : Nat) (snapshot : PendingDestination) (origin : OriginId) (returned : List Carrier)
    (pending : List PendingCarrierFrame)
    (ticket : state.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot))
    (backed : ∀ frame ∈ pending, ∀ carrier ∈ frame.carriers, CarrierResultBacking layout state carrier) :
    ∃ cleaned, exitChannelCleanupBorrowed origin [] [token] false returned state = .ok () cleaned ∧
      ∀ frame ∈ pending, ∀ carrier ∈ frame.carriers, CarrierResultBacking layout cleaned carrier := by
  let cleaned := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! token .released } }
  have released := releaseExitReservation_active state.construction token .fresh incoming selected snapshot ticket
  have cleanup : exitChannelCleanupBorrowed origin [] [token] false returned state = .ok () cleaned := by
    simp only [exitChannelCleanupBorrowed, Bool.false_eq_true, ↓reduceIte, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.forIn_cons, List.forIn_nil, liftConstruction, released, bind, pure]
    rfl
  exact ⟨cleaned, cleanup, fun frame member carrier carried =>
    carrierBacking_release_fresh_ticket layout state token incoming selected snapshot ticket carrier (backed frame member carrier carried)⟩

theorem actual_cleanup_pending_frames (layout : LayoutEnv) (state : ExecutionState)
    (token incoming selected : Nat) (snapshot : PendingDestination) (origin : OriginId) (returned : List Carrier)
    (pending : List PendingCarrierFrame)
    (ticket : state.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot))
    (frames : ∀ frame ∈ pending, CarriersLandingReady state frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking layout state carrier)
    (separate : ∀ frame ∈ pending, .completion token ∉ frame.channels) :
    ∃ cleaned, exitChannelCleanupBorrowed origin [] [token] false returned state = .ok () cleaned ∧
      ∀ frame ∈ pending, CarriersLandingReady cleaned frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking layout cleaned carrier := by
  obtain ⟨cleaned, cleanup, readiness⟩ := actual_cleanup_pending_readiness state token incoming selected snapshot origin returned pending ticket
    (fun frame member => (frames frame member).1) separate
  obtain ⟨other, otherCleanup, backing⟩ := actual_cleanup_pending_backing layout state token incoming selected snapshot origin returned pending ticket
    (fun frame member => (frames frame member).2)
  have same := cleanup.symm.trans otherCleanup
  cases same
  exact ⟨cleaned, cleanup, fun frame member => ⟨readiness frame member, backing frame member⟩⟩

#print axioms actual_cleanup_pending_frames
#print axioms carrierBacking_release_fresh_ticket
#print axioms actual_cleanup_pending_backing

end Goose.Proofs.ConstructionAcceptedExecution
