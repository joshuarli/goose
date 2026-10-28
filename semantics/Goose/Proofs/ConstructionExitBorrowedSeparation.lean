import Goose.Proofs.ConstructionExitTicketUpdate
import Goose.Proofs.ConstructionExitFreshSeparation

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem waiting_ticket_absent_from_ready (state : ExecutionState) (token incoming : Nat)
    (channels : List Channel) (carriers : List Carrier)
    (waiting : state.construction.exitReservations[token]? = some (.waiting incoming))
    (ready : CarriersLandingReady state channels carriers) : .completion token ∉ channels := by
  intro member
  induction channels generalizing carriers with
  | nil => cases member
  | cons channel rest ih =>
    cases carriers with
    | nil => have lengths := ready.lengths; simp at lengths
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
      · subst channel
        cases head with
        | completion token incoming selected source role snapshot ticket sourceReady => cases waiting.symm.trans ticket
        | pendingNamed token incoming selected snapshot ticket => cases waiting.symm.trans ticket
      · exact ih tail tailReady tailMember

theorem borrowed_receipts_pending_separate (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (activation : RuntimeActivation) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized state ambient types live regions pending) :
    ∀ receipt ∈ borrowedExitChannelReceipts activation state,
      ∀ frame ∈ pending, .completion receipt.token ∉ frame.channels := by
  intro receipt member frame present
  obtain ⟨channel, channelMember, captured⟩ := List.mem_filterMap.mp member
  cases channel with
  | register ty => cases captured
  | construct id => cases captured
  | completion token =>
    have source := captureWaitingExitReservation_source token state.construction receipt captured
    exact waiting_ticket_absent_from_ready state receipt.token receipt.incoming frame.channels frame.carriers
      (by simpa only [source.1] using source.2) (world.carriers frame present).1

theorem borrowed_named_step_old_world_pending (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (initial state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (origin : Goose.Core.OriginId) (carriers : List Carrier) (receipt : BorrowedWaitingExitReservation)
    (stage : NamedReservationStage) (incoming selected current : Nat) (snapshot row : PendingDestination)
    (oldWorld : AcceptedWorld config initialized initial ambient types live regions pending)
    (captured : receipt ∈ borrowedExitChannelReceipts activation initial)
    (ticket : state.construction.exitReservations[receipt.token]? = some (.active (.named stage) incoming selected snapshot))
    (resolved : destinationCurrent state.construction receipt.incoming = .ok current)
    (present : state.construction.destinations[current]? = some row)
    (unretained : (carriers.any fun carrier => match carrier with
      | .pendingNamed actual => actual == receipt.token | _ => false) = false)
    (frames : ∀ frame ∈ pending, CarriersLandingReady state frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout state carrier) :
    ∃ after, borrowedExitChannelStep origin carriers receipt state = .ok (ForInStep.yield PUnit.unit) after ∧
      ∀ frame ∈ pending, CarriersLandingReady after frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout after carrier := by
  exact borrowed_named_step_pending config.layout origin carriers receipt state stage incoming selected current snapshot row pending
    ticket resolved present unretained frames
    (borrowed_receipts_pending_separate config initialized initial activation ambient types live regions pending oldWorld receipt captured)

#print axioms borrowed_receipts_pending_separate
#print axioms borrowed_named_step_old_world_pending

end Goose.Proofs.ConstructionAcceptedExecution
