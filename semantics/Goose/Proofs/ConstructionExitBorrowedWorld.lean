import Goose.Proofs.ConstructionExitBorrowedSeparation
import Goose.Proofs.ConstructionExitByteProtectedBuild

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem receivingProtection_update_ticket (layout : LayoutEnv) (state : ExecutionState)
    (live : RootInst → Prop) (region : ReceivingRegion) (token : Nat) (replacement : ExitReservation)
    (protection : ReceivingProtection layout state live region) :
    ReceivingProtection layout { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! token replacement } } live region := by
  let updated := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! token replacement } }
  have prefixes : StoragePrefixesEqual region.limit state.construction.storage updated.construction.storage := by
    intro id
    rfl
  have observations := rootedBackingObservations_storagePrefixes layout state updated _ region.limit
    protection.observations prefixes rfl rfl (by intros; rfl)
  exact ⟨protection.present, observations, protection.cutoff, protection.landing,
    protection.authority, protection.authorityBound, protection.names⟩

theorem rootedBacking_update_ticket (layout : LayoutEnv) (state : ExecutionState) (live : RootInst → Prop)
    (token : Nat) (replacement : ExitReservation) (backed : RootedBackingState layout state live) :
    RootedBackingState layout { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! token replacement } } live := by
  constructor
  · intro root retained value found
    exact valueBacking_update_ticket layout state token replacement value (backed.values root retained value found)
  · exact backed.identities

theorem borrowed_named_step_world_frames (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (initial state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (origin : OriginId) (carriers : List Carrier) (receipt : BorrowedWaitingExitReservation)
    (stage : NamedReservationStage) (incoming selected current : Nat) (snapshot row : PendingDestination)
    (oldWorld : AcceptedWorld config initialized initial ambient types live regions pending)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (captured : receipt ∈ borrowedExitChannelReceipts activation initial)
    (ticket : state.construction.exitReservations[receipt.token]? = some (.active (.named stage) incoming selected snapshot))
    (resolved : destinationCurrent state.construction receipt.incoming = .ok current)
    (present : state.construction.destinations[current]? = some row)
    (unretained : (carriers.any fun carrier => match carrier with
      | .pendingNamed actual => actual == receipt.token | _ => false) = false) :
    ∃ after, borrowedExitChannelStep origin carriers receipt state = .ok (ForInStep.yield PUnit.unit) after ∧
      after.objects = state.objects ∧ after.objectOrdinals = state.objectOrdinals ∧
      RootedBackingState config.layout after live ∧
      (∀ region ∈ regions, ReceivingProtection config.layout after live region) ∧
      ∀ frame ∈ pending, CarriersLandingReady after frame.channels frame.carriers ∧
        ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout after carrier := by
  let updated := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! receipt.token (.waiting receipt.incoming) } }
  have separation := borrowed_receipts_pending_separate config initialized initial activation ambient types live regions pending oldWorld receipt captured
  refine ⟨updated, borrowed_named_step origin carriers receipt state stage incoming selected current snapshot row ticket resolved present unretained,
    rfl, rfl, rootedBacking_update_ticket config.layout state live receipt.token (.waiting receipt.incoming) world.backing, ?_, ?_⟩
  · intro region member
    exact receivingProtection_update_ticket config.layout state live region receipt.token (.waiting receipt.incoming) (world.protections region member)
  · exact ticket_update_pending config.layout state receipt.token (.waiting receipt.incoming) pending world.carriers separation

#print axioms borrowed_named_step_world_frames
#print axioms receivingProtection_update_ticket
#print axioms rootedBacking_update_ticket

end Goose.Proofs.ConstructionAcceptedExecution
