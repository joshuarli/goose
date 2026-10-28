import Goose.Proofs.ConstructionExitMultiFresh
import Goose.Proofs.ConstructionExitReleaseBacking

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem ready_pendingNamed_channel (state : ExecutionState) (channels : List Channel) (carriers : List Carrier)
    (ready : CarriersLandingReady state channels carriers) (token : Nat)
    (member : .pendingNamed token ∈ carriers) : .completion token ∈ channels := by
  induction channels generalizing carriers with
  | nil =>
    have lengths := ready.lengths
    cases carriers <;> simp_all
  | cons channel rest ih =>
    cases carriers with
    | nil => cases member
    | cons carrier tail =>
      have head : CarrierLandingReady state channel carrier := ready.pairs _ _ (by simp)
      have tailReady : CarriersLandingReady state rest tail := by
        refine ⟨?_, ?_⟩
        · simpa only [List.length_cons, Nat.succ.injEq] using ready.lengths
        · intro next item pair
          apply ready.pairs
          simp only [List.zip_cons_cons, List.mem_cons]
          exact Or.inr pair
      rcases List.mem_cons.mp member with equal | tailMember
      · subst carrier
        cases head with
        | pendingNamed token incoming selected snapshot ticket => simp
      · exact List.mem_cons_of_mem _ (ih tail tailReady tailMember)

theorem carrierBacking_release_other_ticket (layout : LayoutEnv) (state : ExecutionState)
    (released : Nat) (carrier : Carrier) (backed : CarrierResultBacking layout state carrier)
    (separate : carrier ≠ .pendingNamed released) :
    CarrierResultBacking layout { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! released .released } } carrier := by
  cases backed with
  | register value backing => exact .register value (valueBacking_release_ticket layout state released value backing)
  | completed id count destination stored present built sampled backing =>
    exact completed_carrier_after_ticket_release layout state released id (.completed id count destination stored present built sampled backing)
  | pendingNamed token incoming selected count snapshot source stored ticket present marked phase sampled backing =>
    have different : released ≠ token := by intro equal; subst token; exact separate rfl
    have unchanged : (state.construction.exitReservations.set! released .released)[token]? = state.construction.exitReservations[token]? := by
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, different]
    have sampled' : storedDestination selected { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! released .released } } = .ok stored
        { state with construction := { state.construction with exitReservations := state.construction.exitReservations.set! released .released } } := by
      simp only [storedDestination, getDestination, EvalM.get, bind, pure] at sampled ⊢
      cases found : state.construction.destinations[selected]? with
      | none => simp [found, fault, EvalM.stop] at sampled
      | some row =>
        simp only [found] at sampled ⊢
        cases progress : progressCount row.progress with
        | none => simp [progress, fault, EvalM.stop] at sampled
        | some n => simp only [progress, ExecutionStep.ok.injEq] at sampled ⊢; exact sampled
    exact .pendingNamed token incoming selected count snapshot source stored
      (by simpa only [unchanged] using ticket) present marked phase sampled' (storedBacking_release_ticket layout state released stored backing)

theorem named_ticket_cancel_release (state : ConstructionState) (token incoming selected : Nat)
    (stage : NamedReservationStage) (snapshot : PendingDestination) (carried : List Nat)
    (ticket : state.exitReservations[token]? = some (.active (.named stage) incoming selected snapshot)) :
    (do cancelExitReservation token carried; releaseExitReservation token) state =
      .ok () { state with exitReservations := state.exitReservations.set! token .released } := by
  have inside := (Array.getElem?_eq_some_iff.mp ticket).1
  have restored : (state.exitReservations.set! token .restored)[token]? = some .restored := by
    rw [Array.set!_eq_setIfInBounds]
    exact Array.getElem?_setIfInBounds_self_of_lt inside
  simp only [cancelExitReservation, ConstructionM.get, ticket, bind, ConstructionM.set,
    releaseExitReservation, restored]
  simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds_setIfInBounds]

theorem named_cancel_release_pending (layout : LayoutEnv) (state : ExecutionState) (token incoming selected : Nat)
    (stage : NamedReservationStage) (snapshot : PendingDestination) (carried : List Nat)
    (pending : List PendingCarrierFrame)
    (ticket : state.construction.exitReservations[token]? = some (.active (.named stage) incoming selected snapshot))
    (frames : ∀ frame ∈ pending, CarriersLandingReady state frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking layout state carrier)
    (separate : ∀ frame ∈ pending, .completion token ∉ frame.channels) :
    let cleaned := { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! token .released } }
    (do cancelExitReservation token carried; releaseExitReservation token) state.construction = .ok () cleaned.construction ∧
      ∀ frame ∈ pending, CarriersLandingReady cleaned frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking layout cleaned carrier := by
  refine ⟨named_ticket_cancel_release state.construction token incoming selected stage snapshot carried ticket, ?_⟩
  intro frame member
  have ready := (frames frame member).1
  refine ⟨carriersReady_release_ticket state token frame.channels frame.carriers ready (separate frame member), ?_⟩
  intro carrier carriedMember
  have different : carrier ≠ .pendingNamed token := by
    intro same
    subst carrier
    exact separate frame member (ready_pendingNamed_channel state frame.channels frame.carriers ready token carriedMember)
  exact carrierBacking_release_other_ticket layout state token carrier ((frames frame member).2 carrier carriedMember) different

#print axioms named_cancel_release_pending
#print axioms ready_pendingNamed_channel
#print axioms carrierBacking_release_other_ticket
#print axioms named_ticket_cancel_release

end Goose.Proofs.ConstructionAcceptedExecution
