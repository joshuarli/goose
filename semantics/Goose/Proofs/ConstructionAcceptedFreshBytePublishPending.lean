import Goose.Proofs.ConstructionAcceptedFreshByteAllFuelGeneral
import Goose.Proofs.ConstructionAcceptedBytePublishWorld

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem fresh_byte_publish_frame_pending (config : EvalConfig) (initialized : Nat) (origin : OriginId)
    (before returned published : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (id count : Nat)
    (row : PendingDestination)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (freshId : id = before.construction.destinations.size)
    (frame : FreshDestinationFrame { returned with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push .released } } returned)
    (present : returned.construction.destinations[id]? = some row)
    (direct : row.backing = .direct before.construction.storage.size)
    (built : row.progress = .built count) (packed : row.layout = .packed)
    (executed : publishCarriers origin [.completed id] returned = .ok () published) :
    Nonempty (FreshDestinationFrame { published with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push .released } } published) ∧
    ∀ pendingFrame ∈ pending, CarriersLandingReady published pendingFrame.channels pendingFrame.carriers ∧
      ∀ carrier ∈ pendingFrame.carriers, CarrierResultBacking config.layout published carrier := by
  subst id
  let baseline := { returned with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push .released } }
  have found : returned.construction.destinations[before.construction.destinations.size]? = some frame.row := by
    rw [frame.destinations]
    exact Array.getElem?_push_size
  have same : row = frame.row := Option.some.inj (present.symm.trans found)
  subst row
  obtain ⟨finalFrame⟩ := frame.publishPacked origin before.construction.storage.size count direct rfl built packed executed
  refine ⟨⟨finalFrame.rebase_runtime (after := published) rfl⟩, ?_⟩
  intro pendingFrame member
  have oldReady := appended_ticket_pending_carrier_ready config initialized before ambient types live regions pending .released world pendingFrame member
  have oldBacking := appended_ticket_pending_carrier_backing config initialized before ambient types live regions pending .released world pendingFrame member
  have baseReady : CarriersLandingReady baseline pendingFrame.channels pendingFrame.carriers :=
    CarriersLandingReady.of_construction_eq (before := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push .released } }) (after := baseline) rfl oldReady
  refine ⟨finalFrame.carriers_ready pendingFrame.channels pendingFrame.carriers baseReady, ?_⟩
  intro carrier present
  have baseBacking : CarrierResultBacking config.layout baseline carrier :=
    CarrierResultBacking.of_construction_eq (before := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push .released } }) (after := baseline) rfl (oldBacking carrier present)
  exact finalFrame.carrier_backing config.layout carrier baseBacking

theorem fresh_byte_publish_preserves_pending (config : EvalConfig) (initialized : Nat) (origin : OriginId)
    (before returned published : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (id count : Nat)
    (row : PendingDestination)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (freshId : id = before.construction.destinations.size)
    (frame : FreshDestinationFrame { returned with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push .released } } returned)
    (present : returned.construction.destinations[id]? = some row)
    (direct : row.backing = .direct before.construction.storage.size)
    (built : row.progress = .built count) (packed : row.layout = .packed)
    (executed : publishCarriers origin [.completed id] returned = .ok () published) :
    ∀ pendingFrame ∈ pending, CarriersLandingReady published pendingFrame.channels pendingFrame.carriers ∧
      ∀ carrier ∈ pendingFrame.carriers, CarrierResultBacking config.layout published carrier := by
  exact (fresh_byte_publish_frame_pending config initialized origin before returned published ambient types live regions pending id count row
    world freshId frame present direct built packed executed).2

#print axioms fresh_byte_publish_frame_pending
#print axioms fresh_byte_publish_preserves_pending
end Goose.Proofs.ConstructionAcceptedExecution
