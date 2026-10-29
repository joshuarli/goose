import Goose.Proofs.ConstructionAcceptedFreshByteWorld
import Goose.Proofs.ConstructionAcceptedFreshReceiving
import Goose.Proofs.ConstructionAcceptedEntryActivation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem fresh_byte_call_prepared_world (config : EvalConfig) (initialized : Nat)
    (caller : RuntimeActivation) (scope : Nat) (allocationOrigin : OriginId) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id : Nat) (activation : RuntimeActivation)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before = .ok id allocated)
    (identifier : activation.act = allocated.nextAct) (channels : activation.channels = [.construct id])
    (newest : id + 1 = allocated.construction.destinations.size)
    (ready : OpenDestinationBacking config.layout allocated id (.varr (.int .u8)) 0)
    (current : destinationCurrent allocated.construction id = .ok id)
    (history : ReservationReferencesBounded allocated.construction ambient)
    (separated : ∀ retained ∈ completedCarrierIds ambient.retained,
      destinationDescendant allocated.construction.destinations id retained = false) :
    let pushed := { allocated with nextAct := allocated.nextAct + 1, activations := activation :: allocated.activations }
    let scopeState := ownershipResultScopeState activation scope pushed
    let prepared := { scopeState with construction := { scopeState.construction with
      exitReservations := scopeState.construction.exitReservations.push (.active .fresh id id ready.destination) } }
    AcceptedWorld config initialized prepared
      (.exitChannels [scopeState.construction.exitReservations.size] [] [.completed id] :: .callChannels activation [] :: ambient)
      types live (freshReceivingRegion before id :: regions) pending ∧
    prepared.objects = before.objects ∧ prepared.objectOrdinals = before.objectOrdinals := by
  let pushed := { allocated with nextAct := allocated.nextAct + 1, activations := activation :: allocated.activations }
  let scopeState := ownershipResultScopeState activation scope pushed
  let prepared := { scopeState with construction := { scopeState.construction with
    exitReservations := scopeState.construction.exitReservations.push (.active .fresh id id ready.destination) } }
  have allocatedWorld := newDestination_acceptedWorld config caller.act (.varr (.int .u8)) .value allocationOrigin knownCount initialized
    before allocated id ambient types live regions pending world created
  have pushedWorld := acceptedWorld_pushNewestConstructActivation config initialized allocated ambient types live
    (freshReceivingRegion before id :: regions) pending activation id allocatedWorld identifier channels newest current
  have scopedWorld := acceptedWorld_resultScope config initialized pushed (.callChannels activation [] :: ambient) types live
    (freshReceivingRegion before id :: regions) pending activation scope pushedWorld
  have scopedHistory : ReservationReferencesBounded scopeState.construction (.callChannels activation [] :: ambient) := by
    intro frame member
    rcases List.mem_cons.mp member with same | old
    · subst frame
      simp [OwnershipAmbientFrame.tickets, channels]
    · exact history frame old
  have scopedSeparated : ∀ retained ∈ completedCarrierIds (OwnershipAmbient.retained (.callChannels activation [] :: ambient)),
      destinationDescendant scopeState.construction.destinations id retained = false := by
    intro retained member
    apply separated retained
    simpa [OwnershipAmbient.retained, OwnershipAmbientFrame.carriers] using member
  have readyWorld := direct_fresh_acceptedWorld_pending config initialized scopeState (.callChannels activation [] :: ambient) types live
    (freshReceivingRegion before id :: regions) pending id ready.destination [.completed id] scopedWorld scopedHistory
    ready.present ready.opened current scopedSeparated
  obtain ⟨frame⟩ := newDestination_fresh_frame config.layout caller.act (.varr (.int .u8)) .value allocationOrigin knownCount
    before allocated id world.ownership.source.structural.1.1.1 created
  have objects := congrArg ExecutionState.objects frame.outer
  have ordinals := congrArg ExecutionState.objectOrdinals frame.outer
  exact ⟨readyWorld, objects, ordinals⟩

#print axioms fresh_byte_call_prepared_world
end Goose.Proofs.ConstructionAcceptedExecution
