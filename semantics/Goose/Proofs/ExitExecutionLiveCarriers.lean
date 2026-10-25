import Goose.Proofs.ExitExecutionCommitLanding
import Goose.Proofs.ConstructionRootedBacking

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

inductive CarrierResultBacking (layout : LayoutEnv) (state : ExecutionState) : Carrier → Prop
  | register (value : Value) (backed : ValueStorageBacked layout state value) :
      CarrierResultBacking layout state (.register value)
  | completed (id count : Nat) (destination : PendingDestination) (stored : StoredValue)
      (present : state.construction.destinations[id]? = some destination)
      (built : destination.progress = .built count)
      (sampled : storedDestination id state = .ok stored state)
      (backed : StoredValueBacking layout state stored) :
      CarrierResultBacking layout state (.completed id)
  | pendingNamed (token incoming selected count : Nat) (snapshot source : PendingDestination)
      (stored : StoredValue)
      (ticket : state.construction.exitReservations[token]? = some (.active (.named .ready) incoming selected snapshot))
      (present : state.construction.destinations[selected]? = some source)
      (marked : { source with progress := .built count } = snapshot)
      (phase : source.progress = .built count ∨
        (∃ child, source.progress = .suspended count child) ∨ ∃ replacement, source.progress = .exiting count replacement)
      (sampled : storedDestination selected state = .ok stored state)
      (backed : StoredValueBacking layout state stored) :
      CarrierResultBacking layout state (.pendingNamed token)

structure ReceivingCarrierLandingReady (state : ExecutionState) (incoming source : Nat) where
  receiving : Nat
  sourceDestination : PendingDestination
  receivingDestination : PendingDestination
  resolved : destinationCurrent state.construction incoming = .ok receiving
  sourcePresent : state.construction.destinations[source]? = some sourceDestination
  receivingPresent : state.construction.destinations[receiving]? = some receivingDestination
  path : OwnershipReplacementPath state.construction.destinations receiving source
  parent : LandingParentReady state.construction receiving receivingDestination
  ordered : receivingDestination.capability.start ≤ sourceDestination.capability.start

inductive CarrierLandingReady (state : ExecutionState) : Channel → Carrier → Prop
  | register (ty : Ty) (value : Value) : CarrierLandingReady state (.register ty) (.register value)
  | construct (incoming source : Nat) (ready : ReceivingCarrierLandingReady state incoming source) :
      CarrierLandingReady state (.construct incoming) (.completed source)
  | completion (token incoming selected source : Nat) (role : ExitReservationRole) (snapshot : PendingDestination)
      (ticket : state.construction.exitReservations[token]? = some (.active role incoming selected snapshot))
      (ready : ReceivingCarrierLandingReady state selected source) :
      CarrierLandingReady state (.completion token) (.completed source)
  | pendingNamed (token incoming selected : Nat) (snapshot : PendingDestination)
      (ticket : state.construction.exitReservations[token]? = some (.active (.named .ready) incoming selected snapshot)) :
      CarrierLandingReady state (.completion token) (.pendingNamed token)

structure CarriersLandingReady (state : ExecutionState) (channels : List Channel) (carriers : List Carrier) : Prop where
  lengths : channels.length = carriers.length
  pairs : ∀ channel carrier, (channel, carrier) ∈ channels.zip carriers → CarrierLandingReady state channel carrier

theorem landCarriersInto_current (origin : Goose.Core.OriginId) (state : ExecutionState)
    (incoming source : Nat) (ready : ReceivingCarrierLandingReady state incoming source)
    (current : ready.receiving = source) :
    landCarriersInto origin [.construct incoming] [.completed source] state = .ok () state := by
  have resolved : destinationCurrent state.construction incoming = .ok source := by simpa only [current] using ready.resolved
  simp only [landCarriersInto, List.length_cons, List.length_nil, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons,
    List.forIn_nil, receivingDestination, liftConstruction, resolved, bind, pure]

#print axioms landCarriersInto_current

end Goose.Proofs.ExitExecution
