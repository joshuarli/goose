import Goose.Proofs.ConstructionAcceptedPendingConstruction
import Goose.Proofs.ConstructionAcceptedByteFrame

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

def FreshDestinationFrame.appended_ticket_rebase {before allocated prepared : ExecutionState}
    (frame : FreshDestinationFrame before allocated) (reservation : ExitReservation)
    (construction : prepared.construction = { allocated.construction with
      exitReservations := allocated.construction.exitReservations.push reservation }) :
    let baseline := { prepared with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push reservation } }
    FreshDestinationFrame baseline prepared := by
  let baseline := { prepared with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push reservation } }
  refine ⟨rfl, frame.row, ?_, frame.receiver, ?_, ?_, ?_⟩
  · simpa only [baseline, construction] using frame.destinations
  · simpa only [baseline, construction] using frame.successors
  · simp only [construction, frame.tickets]
  · intro id storage found
    simpa only [baseline, construction] using frame.storage id storage found

theorem fresh_byte_build_frame (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (caller producer : RuntimeActivation) (bytes : List UInt8) (allocationOrigin origin : OriginId) (knownCount : Option Nat)
    (before allocated prepared after : ExecutionState) (id : Nat) (reservation : ExitReservation)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (source : OwnershipSourceState prepared.construction)
    (created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before = .ok id allocated)
    (construction : prepared.construction = { allocated.construction with
      exitReservations := allocated.construction.exitReservations.push reservation })
    (current : destinationCurrent prepared.construction id = .ok id)
    (executed : buildExpr (fuel + 1) config producer id (.bytes (.varr (.int .u8)) bytes origin) prepared = .ok () after) :
    Nonempty (FreshDestinationFrame { prepared with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push reservation } } after) := by
  have freshId := newDestination_fresh_id config.layout caller.act (.varr (.int .u8)) .value allocationOrigin knownCount before allocated id created
  subst id
  obtain ⟨originalFrame⟩ := newDestination_fresh_frame config.layout caller.act (.varr (.int .u8)) .value allocationOrigin knownCount
    before allocated before.construction.destinations.size world.ownership.source.structural.1.1.1 created
  let baseline := { prepared with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push reservation } }
  let initialFrame : FreshDestinationFrame baseline prepared := originalFrame.appended_ticket_rebase reservation construction
  obtain ⟨initialReady⟩ := newDestination_initial_backing config.layout caller.act (.varr (.int .u8)) .value allocationOrigin knownCount
    before allocated before.construction.destinations.size (.int .u8) rfl created
  have preparedPresent : prepared.construction.destinations[before.construction.destinations.size]? = some initialReady.destination := by
    simpa only [construction] using initialReady.present
  have preparedBytes : prepared.construction.storage[initialReady.destination.storage]? = some initialReady.storage := by
    simpa only [construction] using initialReady.bytes
  let ready : OpenDestinationBacking config.layout prepared before.construction.destinations.size (.varr (.int .u8)) 0 :=
    { initialReady with present := preparedPresent, bytes := preparedBytes }
  obtain ⟨row, found, packed, request, direct, receiver⟩ :=
    newDestination_byteOwner_packed_value config.layout caller.act allocationOrigin knownCount before allocated before.construction.destinations.size created
  have frameFound : allocated.construction.destinations[before.construction.destinations.size]? = some originalFrame.row := by
    rw [originalFrame.destinations]
    exact Array.getElem?_push_size
  have sameRow : row = originalFrame.row := Option.some.inj (found.symm.trans frameFound)
  subst row
  obtain ⟨nextFrame, nextDirect⟩ := buildExpr_byteOwner_freshFrame fuel config producer bytes origin baseline prepared after initialFrame
    before.construction.storage.size 0 ready (by simpa [initialFrame, FreshDestinationFrame.appended_ticket_rebase] using direct) rfl
    (by simpa [initialFrame, FreshDestinationFrame.appended_ticket_rebase] using packed)
    (by simpa [initialFrame, FreshDestinationFrame.appended_ticket_rebase] using request) source.structural.1.1.1 current executed
  exact ⟨nextFrame⟩

theorem fresh_byte_build_preserves_pending (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (caller producer : RuntimeActivation) (bytes : List UInt8) (allocationOrigin origin : OriginId) (knownCount : Option Nat)
    (before allocated prepared after : ExecutionState) (id : Nat) (reservation : ExitReservation)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (source : OwnershipSourceState prepared.construction)
    (created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before = .ok id allocated)
    (construction : prepared.construction = { allocated.construction with
      exitReservations := allocated.construction.exitReservations.push reservation })
    (current : destinationCurrent prepared.construction id = .ok id)
    (executed : buildExpr (fuel + 1) config producer id (.bytes (.varr (.int .u8)) bytes origin) prepared = .ok () after) :
    ∀ frame ∈ pending, CarriersLandingReady after frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout after carrier := by
  let baseline := { prepared with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push reservation } }
  obtain ⟨nextFrame⟩ := fresh_byte_build_frame fuel config initialized caller producer bytes allocationOrigin origin knownCount
    before allocated prepared after id reservation ambient types live regions pending world source created construction current executed
  intro pendingFrame member
  have oldReady := appended_ticket_pending_carrier_ready config initialized before ambient types live regions pending reservation world pendingFrame member
  have oldBacking := appended_ticket_pending_carrier_backing config initialized before ambient types live regions pending reservation world pendingFrame member
  have baseReady : CarriersLandingReady baseline pendingFrame.channels pendingFrame.carriers :=
    CarriersLandingReady.of_construction_eq (before := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push reservation } }) (after := baseline) rfl oldReady
  refine ⟨nextFrame.carriers_ready pendingFrame.channels pendingFrame.carriers baseReady, ?_⟩
  intro carrier present
  have baseBacking : CarrierResultBacking config.layout baseline carrier :=
    CarrierResultBacking.of_construction_eq (before := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push reservation } }) (after := baseline) rfl (oldBacking carrier present)
  exact nextFrame.carrier_backing config.layout carrier baseBacking

#print axioms FreshDestinationFrame.appended_ticket_rebase
#print axioms fresh_byte_build_frame
#print axioms fresh_byte_build_preserves_pending
end Goose.Proofs.ConstructionAcceptedExecution
