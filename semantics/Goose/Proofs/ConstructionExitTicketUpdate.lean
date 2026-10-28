import Goose.Proofs.ConstructionExitNamedCleanup
import Goose.Proofs.ConstructionExitBorrowedNamedStep

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

def receivingCarrierReady_update_ticket (state : ExecutionState) (released : Nat) (replacement : ExitReservation) (incoming source : Nat)
    (ready : ReceivingCarrierLandingReady state incoming source) :
    ReceivingCarrierLandingReady { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! released replacement } } incoming source := by
  have current := destinationCurrent_congr_tables state.construction
    { state.construction with exitReservations := state.construction.exitReservations.set! released replacement } rfl rfl incoming
  have parent : LandingParentReady { state.construction with exitReservations := state.construction.exitReservations.set! released replacement } ready.receiving ready.receivingDestination := by
    cases ready.parent with
    | receiver use => exact .receiver use
    | child parentId count parent use present progress => exact .child parentId count parent use present progress
    | replacement parentId count parent use present progress => exact .replacement parentId count parent use present progress
  exact ⟨ready.receiving, ready.sourceDestination, ready.receivingDestination,
    current.trans ready.resolved, ready.sourcePresent, ready.receivingPresent, ready.path, parent, ready.ordered⟩

theorem carriersReady_update_ticket (state : ExecutionState) (released : Nat) (replacement : ExitReservation) (channels : List Channel) (carriers : List Carrier)
    (ready : CarriersLandingReady state channels carriers) (separate : .completion released ∉ channels) :
    CarriersLandingReady { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! released replacement } } channels carriers := by
  refine ⟨ready.lengths, ?_⟩
  intro channel carrier member
  have previous := ready.pairs channel carrier member
  cases previous with
  | register ty value => exact .register ty value
  | construct incoming source sourceReady => exact .construct incoming source (receivingCarrierReady_update_ticket state released replacement incoming source sourceReady)
  | completion token incoming selected source role snapshot ticket sourceReady =>
    have channelMember : Channel.completion token ∈ channels := (List.of_mem_zip member).1
    have different : released ≠ token := by
      intro same
      subst token
      exact separate channelMember
    have unchanged : (state.construction.exitReservations.set! released replacement)[token]? =
        state.construction.exitReservations[token]? := by
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, different]
    exact .completion token incoming selected source role snapshot (by simpa only [unchanged] using ticket)
      (receivingCarrierReady_update_ticket state released replacement selected source sourceReady)
  | pendingNamed token incoming selected snapshot ticket =>
    have channelMember : Channel.completion token ∈ channels := (List.of_mem_zip member).1
    have different : released ≠ token := by
      intro same
      subst token
      exact separate channelMember
    have unchanged : (state.construction.exitReservations.set! released replacement)[token]? =
        state.construction.exitReservations[token]? := by
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, different]
    exact .pendingNamed token incoming selected snapshot (by simpa only [unchanged] using ticket)

theorem storedBacking_update_ticket (layout : LayoutEnv) (state : ExecutionState) (released : Nat) (replacement : ExitReservation)
    (stored : StoredValue) (backed : StoredValueBacking layout state stored) :
    StoredValueBacking layout { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! released replacement } } stored := by
  cases backed with
  | detached storage element present detached ty interval => exact .detached storage element present detached ty interval
  | named id storage destination count present named binding backing ty start progress element elementType interval =>
    exact .named id storage destination count present named binding backing ty start progress element elementType interval

theorem valueBacking_update_ticket (layout : LayoutEnv) (state : ExecutionState) (released : Nat) (replacement : ExitReservation)
    (value : Value) (backed : ValueStorageBacked layout state value) :
    ValueStorageBacked layout { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! released replacement } } value := by
  induction backed with
  | integer ty value => exact .integer ty value
  | boolean value => exact .boolean value
  | unit => exact .unit
  | reference location => exact .reference location
  | slice location start count => exact .slice location start count
  | array values children ih => exact .array values ih
  | record id values children ih => exact .record id values ih
  | stored value backed => exact .stored value (storedBacking_update_ticket layout state released replacement value backed)

theorem carrierBacking_update_other_ticket (layout : LayoutEnv) (state : ExecutionState)
    (released : Nat) (replacement : ExitReservation) (carrier : Carrier) (backed : CarrierResultBacking layout state carrier)
    (separate : carrier ≠ .pendingNamed released) :
    CarrierResultBacking layout { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! released replacement } } carrier := by
  cases backed with
  | register value backing => exact .register value (valueBacking_update_ticket layout state released replacement value backing)
  | completed id count destination stored present built sampled backing =>
    refine .completed id count destination stored present built ?_ (storedBacking_update_ticket layout state released replacement stored backing)
    simp only [storedDestination, getDestination, EvalM.get, bind, pure] at sampled ⊢
    cases found : state.construction.destinations[id]? with
    | none => simp [found, fault, EvalM.stop] at sampled
    | some row =>
      simp only [found] at sampled ⊢
      cases progress : progressCount row.progress with
      | none => simp [progress, fault, EvalM.stop] at sampled
      | some n => simp only [progress, ExecutionStep.ok.injEq] at sampled ⊢; exact sampled
  | pendingNamed token incoming selected count snapshot source stored ticket present marked phase sampled backing =>
    have different : released ≠ token := by intro equal; subst token; exact separate rfl
    have unchanged : (state.construction.exitReservations.set! released replacement)[token]? = state.construction.exitReservations[token]? := by
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, different]
    have sampled' : storedDestination selected { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! released replacement } } = .ok stored
        { state with construction := { state.construction with exitReservations := state.construction.exitReservations.set! released replacement } } := by
      simp only [storedDestination, getDestination, EvalM.get, bind, pure] at sampled ⊢
      cases found : state.construction.destinations[selected]? with
      | none => simp [found, fault, EvalM.stop] at sampled
      | some row =>
        simp only [found] at sampled ⊢
        cases progress : progressCount row.progress with
        | none => simp [progress, fault, EvalM.stop] at sampled
        | some n => simp only [progress, ExecutionStep.ok.injEq] at sampled ⊢; exact sampled
    exact .pendingNamed token incoming selected count snapshot source stored
      (by simpa only [unchanged] using ticket) present marked phase sampled' (storedBacking_update_ticket layout state released replacement stored backing)

theorem ticket_update_pending (layout : LayoutEnv) (state : ExecutionState) (token : Nat)
    (replacement : ExitReservation) (pending : List PendingCarrierFrame)
    (frames : ∀ frame ∈ pending, CarriersLandingReady state frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking layout state carrier)
    (separate : ∀ frame ∈ pending, .completion token ∉ frame.channels) :
    ∀ frame ∈ pending, CarriersLandingReady { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! token replacement } } frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking layout { state with construction := { state.construction with
        exitReservations := state.construction.exitReservations.set! token replacement } } carrier := by
  intro frame member
  have ready := (frames frame member).1
  refine ⟨carriersReady_update_ticket state token replacement frame.channels frame.carriers ready (separate frame member), ?_⟩
  intro carrier carried
  have different : carrier ≠ .pendingNamed token := by
    intro same
    subst carrier
    exact separate frame member (ready_pendingNamed_channel state frame.channels frame.carriers ready token carried)
  exact carrierBacking_update_other_ticket layout state token replacement carrier ((frames frame member).2 carrier carried) different

theorem borrowed_named_step_pending (layout : LayoutEnv) (origin : Goose.Core.OriginId) (carriers : List Carrier)
    (receipt : BorrowedWaitingExitReservation) (state : ExecutionState)
    (stage : NamedReservationStage) (incoming selected current : Nat) (snapshot row : PendingDestination)
    (pending : List PendingCarrierFrame)
    (ticket : state.construction.exitReservations[receipt.token]? = some (.active (.named stage) incoming selected snapshot))
    (resolved : destinationCurrent state.construction receipt.incoming = .ok current)
    (present : state.construction.destinations[current]? = some row)
    (unretained : (carriers.any fun carrier => match carrier with
      | .pendingNamed actual => actual == receipt.token | _ => false) = false)
    (frames : ∀ frame ∈ pending, CarriersLandingReady state frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking layout state carrier)
    (separate : ∀ frame ∈ pending, .completion receipt.token ∉ frame.channels) :
    ∃ after, borrowedExitChannelStep origin carriers receipt state = .ok (ForInStep.yield PUnit.unit) after ∧
      ∀ frame ∈ pending, CarriersLandingReady after frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking layout after carrier := by
  exact ⟨_, borrowed_named_step origin carriers receipt state stage incoming selected current snapshot row ticket resolved present unretained,
    ticket_update_pending layout state receipt.token (.waiting receipt.incoming) pending frames separate⟩

#print axioms borrowed_named_step_pending
#print axioms ticket_update_pending
#print axioms carriersReady_update_ticket
#print axioms carrierBacking_update_other_ticket

end Goose.Proofs.ConstructionAcceptedExecution
