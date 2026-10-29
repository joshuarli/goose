import Goose.Proofs.ConstructionExitWaitingAcceptedFrame
import Goose.Proofs.ExitExecutionLiveCarriers

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem appended_ticket_pending_carrier_ready (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (reservation : ExitReservation)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (frame : PendingCarrierFrame) (member : frame ∈ pending) :
    let waited := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push reservation } }
    CarriersLandingReady waited frame.channels frame.carriers := by
  let waited := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push reservation } }
  have oldTicket (id : Nat) (status : ExitReservation) (present : before.construction.exitReservations[id]? = some status) :
      waited.construction.exitReservations[id]? = some status := by
    have inside := (Array.getElem?_eq_some_iff.mp present).1
    simpa [waited, Array.getElem?_push, Nat.ne_of_lt inside] using present
  have receiving (channel id : Nat) (ready : ReceivingCarrierLandingReady before channel id) :
      ReceivingCarrierLandingReady waited channel id := by
    refine ⟨ready.receiving, ready.sourceDestination, ready.receivingDestination, ?_, ready.sourcePresent,
      ready.receivingPresent, ready.path, ?_, ready.ordered⟩
    · rw [destinationCurrent_congr_tables before.construction waited.construction rfl rfl channel]
      exact ready.resolved
    · cases ready.parent with
      | receiver use => exact .receiver use
      | child parent count row use present progress => exact .child parent count row use present progress
      | replacement parent count row use present progress => exact .replacement parent count row use present progress
  have original := (world.carriers frame member).1
  refine ⟨original.lengths, ?_⟩
  intro channel carrier pair
  have ready := original.pairs channel carrier pair
  cases ready with
  | register ty value => exact .register ty value
  | pendingNamed token oldIncoming selected snapshot ticket =>
    exact .pendingNamed token oldIncoming selected snapshot (oldTicket token _ ticket)
  | construct channel id ready =>
    exact .construct channel id (receiving channel id ready)
  | completion token oldIncoming selected id role snapshot ticket ready =>
    exact .completion token oldIncoming selected id role snapshot (oldTicket token _ ticket) (receiving selected id ready)

theorem waiting_pending_carrier_ready (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (incoming : Nat)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (frame : PendingCarrierFrame) (member : frame ∈ pending) :
    let waited := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.waiting incoming) } }
    waitExitDestination incoming before.construction = .ok before.construction.exitReservations.size waited.construction ∧
    CarriersLandingReady waited frame.channels frame.carriers := by
  refine ⟨?_, appended_ticket_pending_carrier_ready config initialized before ambient types live regions pending (.waiting incoming) world frame member⟩
  simp [waitExitDestination, ConstructionM.get, ConstructionM.set, bind, pure]

theorem appended_ticket_pending_carrier_backing (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (reservation : ExitReservation)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (frame : PendingCarrierFrame) (member : frame ∈ pending) :
    let waited := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push reservation } }
    ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout waited carrier := by
  let waited := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push reservation } }
  have oldTicket (id : Nat) (status : ExitReservation) (present : before.construction.exitReservations[id]? = some status) :
      waited.construction.exitReservations[id]? = some status := by
    have inside := (Array.getElem?_eq_some_iff.mp present).1
    simpa [waited, Array.getElem?_push, Nat.ne_of_lt inside] using present
  have storedBacking (stored : StoredValue) (backed : StoredValueBacking config.layout before stored) :
      StoredValueBacking config.layout waited stored := by
    cases backed with
    | detached storage element present detached type interval => exact .detached storage element present detached type interval
    | named id storage destination count present named binding backing type start progress element elementType interval =>
      exact .named id storage destination count present named binding backing type start progress element elementType interval
  have valueBacking (value : Value) (backed : ValueStorageBacked config.layout before value) :
      ValueStorageBacked config.layout waited value := by
    induction backed with
    | integer ty value => exact .integer ty value
    | boolean value => exact .boolean value
    | unit => exact .unit
    | reference location => exact .reference location
    | slice location start count => exact .slice location start count
    | stored value backed => exact .stored value (storedBacking value backed)
    | array values children ih => exact .array values ih
    | record id values children ih => exact .record id values ih
  have sample (id : Nat) (stored : StoredValue) (prior : storedDestination id before = .ok stored before) :
      storedDestination id waited = .ok stored waited := by
    cases found : before.construction.destinations[id]? with
    | none => simp [storedDestination, getDestination, EvalM.get, found, bind, fault, EvalM.stop] at prior
    | some destination =>
      cases phase : progressCount destination.progress with
      | none => simp [storedDestination, getDestination, EvalM.get, found, bind, pure, phase, fault, EvalM.stop] at prior
      | some count =>
        simp [storedDestination, getDestination, EvalM.get, found, bind, phase, pure, waited] at prior ⊢
        exact prior
  change ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout waited carrier
  intro carrier present
  have backed := (world.carriers frame member).2 carrier present
  cases backed with
  | register value backed => exact .register value (valueBacking value backed)
  | completed id count destination stored found built sampled backed =>
    exact .completed id count destination stored found built (sample id stored sampled) (storedBacking stored backed)
  | pendingNamed token oldIncoming selected count snapshot source stored ticket found marked phase sampled backed =>
    exact .pendingNamed token oldIncoming selected count snapshot source stored (oldTicket token _ ticket) found marked phase
      (sample selected stored sampled) (storedBacking stored backed)

theorem waiting_pending_carrier_backing (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (incoming : Nat)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (frame : PendingCarrierFrame) (member : frame ∈ pending) :
    let waited := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.waiting incoming) } }
    ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout waited carrier := by
  exact appended_ticket_pending_carrier_backing config initialized before ambient types live regions pending (.waiting incoming) world frame member

#print axioms appended_ticket_pending_carrier_ready
#print axioms appended_ticket_pending_carrier_backing
#print axioms waiting_pending_carrier_backing

#print axioms waiting_pending_carrier_ready

end Goose.Proofs.ConstructionAcceptedExecution
