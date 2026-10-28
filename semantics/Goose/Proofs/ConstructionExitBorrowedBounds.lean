import Goose.Proofs.ConstructionExitBorrowedOwnership

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ExitExecution

theorem channel_bound_after_waiting_update (state : ConstructionState) (token incoming current : Nat)
    (channel : Channel) (resolved : destinationCurrent state incoming = .ok current)
    (valid : OwnershipChannelReceivingBound state channel) :
    OwnershipChannelReceivingBound { state with exitReservations := state.exitReservations.set! token (.waiting incoming) } channel := by
  cases channel with
  | register ty => trivial
  | construct id => exact valid
  | completion index =>
    intro other ticket
    by_cases same : token = index
    · subst index
      have inside := destinationCurrent_bounds state incoming current resolved
      have tokenInside := (Array.getElem?_eq_some_iff.mp ticket).1
      have exactTicket : (state.exitReservations.set! token (.waiting incoming))[token]? = some (.waiting incoming) := by
        rw [Array.set!_eq_setIfInBounds] at ticket ⊢
        exact Array.getElem?_setIfInBounds_self_of_lt (by simpa using tokenInside)
      have equal := Option.some.inj (ticket.symm.trans exactTicket)
      cases equal
      change incoming < state.destinations.size
      exact Nat.lt_of_le_of_lt inside.1 inside.2
    · have old : state.exitReservations[index]? = some (.waiting other) := by
        simpa [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, same] using ticket
      exact valid other old

theorem captured_bounds_after_waiting_update (state : ConstructionState) (token incoming current : Nat)
    (ambient : OwnershipAmbient) (resolved : destinationCurrent state incoming = .ok current)
    (bounds : OwnershipCapturedReceivingBounds state ambient) :
    OwnershipCapturedReceivingBounds { state with exitReservations := state.exitReservations.set! token (.waiting incoming) } ambient := by
  induction ambient with
  | nil => trivial
  | cons frame outer ih =>
    have tail := ih bounds.2
    refine ⟨?_, tail⟩
    cases frame <;> try trivial
    case receivingScope capture carriers =>
      exact channel_bound_after_waiting_update state token incoming current (.construct capture.incoming) resolved bounds.1
    all_goals intro channel member; exact channel_bound_after_waiting_update state token incoming current channel resolved (bounds.1 channel member)

theorem borrowed_named_step_source_bounds (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (initial state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (origin : Goose.Core.OriginId) (carriers : List Carrier) (receipt : BorrowedWaitingExitReservation)
    (stage : NamedReservationStage) (incoming selected current : Nat) (snapshot row : PendingDestination)
    (oldWorld : AcceptedWorld config initialized initial ambient types live regions pending)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (captured : receipt ∈ Goose.Proofs.ExitExecution.borrowedExitChannelReceipts activation initial)
    (ticket : state.construction.exitReservations[receipt.token]? = some (.active (.named stage) incoming selected snapshot))
    (resolved : destinationCurrent state.construction receipt.incoming = .ok current)
    (present : state.construction.destinations[current]? = some row)
    (unretained : (carriers.any fun carrier => match carrier with
      | .pendingNamed actual => actual == receipt.token | _ => false) = false) :
    ∃ after, Goose.Proofs.ExitExecution.borrowedExitChannelStep origin carriers receipt state = .ok (ForInStep.yield PUnit.unit) after ∧
      OwnershipSourceState after.construction ∧ OwnershipCapturedReceivingBounds after.construction ambient ∧
      Goose.Proofs.ConstructionRepresentation.RootedBackingState config.layout after live ∧
      (∀ region ∈ regions, ReceivingProtection config.layout after live region) ∧
      ∀ frame ∈ pending, Goose.Proofs.ExitExecution.CarriersLandingReady after frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, Goose.Proofs.ExitExecution.CarrierResultBacking config.layout after carrier := by
  let updated := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! receipt.token (.waiting receipt.incoming) } }
  have step := borrowed_named_step origin carriers receipt state stage incoming selected current snapshot row ticket resolved present unretained
  have source := waiting_update_source state.construction receipt stage incoming selected current snapshot row ticket resolved present world.ownership.source
  have bounds := captured_bounds_after_waiting_update state.construction receipt.token receipt.incoming current ambient resolved world.ownership.bounds
  have separation := borrowed_receipts_pending_separate config initialized initial activation ambient types live regions pending oldWorld receipt captured
  refine ⟨updated, step, source, bounds, rootedBacking_update_ticket config.layout state live receipt.token (.waiting receipt.incoming) world.backing, ?_, ?_⟩
  · intro region member
    exact receivingProtection_update_ticket config.layout state live region receipt.token (.waiting receipt.incoming) (world.protections region member)
  · exact ticket_update_pending config.layout state receipt.token (.waiting receipt.incoming) pending world.carriers separation

#print axioms borrowed_named_step_source_bounds
#print axioms channel_bound_after_waiting_update
#print axioms captured_bounds_after_waiting_update

end Goose.Proofs.ConstructionAcceptedExecution
