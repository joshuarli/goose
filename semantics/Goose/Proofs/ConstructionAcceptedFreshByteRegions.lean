import Goose.Proofs.ConstructionAcceptedFreshBytePending
import Goose.Proofs.ConstructionExitDirectFreshWorld

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem ReceivingProtection.appended_ticket (layout : LayoutEnv) (before : ExecutionState)
    (live : RootInst → Prop) (region : ReceivingRegion) (reservation : ExitReservation)
    (protection : ReceivingProtection layout before live region) :
    ReceivingProtection layout { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push reservation } } live region := by
  refine ⟨protection.present, ?_, protection.cutoff, protection.landing, protection.authority,
    protection.authorityBound, protection.names⟩
  refine ⟨⟨?_, protection.observations.backing.identities⟩, ?_⟩
  · intro root kept value found
    exact appended_ticket_value_backing layout before reservation value (protection.observations.backing.values root kept value found)
  · intro root kept value found stored occurrence
    exact appended_ticket_stored_observation layout before reservation region.limit stored
      (protection.observations.observations root kept value found stored occurrence)

theorem ReceivingProtection.state_frame (layout : LayoutEnv) (before after : ExecutionState)
    (live : RootInst → Prop) (region : ReceivingRegion)
    (construction : after.construction = before.construction)
    (objects : after.objects = before.objects) (ordinals : after.objectOrdinals = before.objectOrdinals)
    (protection : ReceivingProtection layout before live region) : ReceivingProtection layout after live region := by
  refine ⟨?_, ?_, ?_, ?_, protection.authority, ?_, ?_⟩
  · simpa only [construction] using protection.present
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro root kept value found
      exact (protection.observations.backing.values root kept value (by simpa only [objects] using found)).construction_frame construction
    · intro root kept stored found
      simpa only [ordinals] using protection.observations.backing.identities root kept stored (by simpa only [objects] using found)
    · intro root kept value found stored occurrence
      exact (protection.observations.observations root kept value (by simpa only [objects] using found) stored occurrence).construction_frame layout before after region.limit stored construction
  · intro row found
    exact protection.cutoff row (by simpa only [construction] using found)
  · intro row found
    exact protection.landing row (by simpa only [construction] using found)
  · intro id member
    simpa only [construction] using protection.authorityBound id member
  · intro root kept outside value found stored occurrence id named mutable
    exact protection.names root kept outside value (by simpa only [objects] using found) stored occurrence id named mutable

theorem fresh_byte_build_preserves_regions (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (caller producer : RuntimeActivation) (bytes : List UInt8) (allocationOrigin origin : OriginId) (knownCount : Option Nat)
    (before allocated prepared after : ExecutionState) (id : Nat) (reservation : ExitReservation)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (source : OwnershipSourceState prepared.construction)
    (created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before = .ok id allocated)
    (construction : prepared.construction = { allocated.construction with
      exitReservations := allocated.construction.exitReservations.push reservation })
    (objects : prepared.objects = before.objects) (ordinals : prepared.objectOrdinals = before.objectOrdinals)
    (current : destinationCurrent prepared.construction id = .ok id)
    (executed : buildExpr (fuel + 1) config producer id (.bytes (.varr (.int .u8)) bytes origin) prepared = .ok () after) :
    ∀ region ∈ regions, ReceivingProtection config.layout after live region := by
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
  intro region member
  let original := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push reservation } }
  have initial : ReceivingProtection config.layout baseline live region :=
    (world.protections region member).appended_ticket config.layout before live region reservation |>.state_frame
      config.layout original baseline live region rfl objects ordinals
  exact nextFrame.protection config.layout live region initial

#print axioms fresh_byte_build_preserves_regions
#print axioms ReceivingProtection.appended_ticket
#print axioms ReceivingProtection.state_frame
end Goose.Proofs.ConstructionAcceptedExecution
