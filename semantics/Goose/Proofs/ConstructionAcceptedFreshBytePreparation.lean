import Goose.Proofs.ConstructionAcceptedFreshByteWorld
import Goose.Proofs.ConstructionAcceptedRetainedBounds
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

theorem fresh_byte_call_prepared_world_bounded (config : EvalConfig) (initialized : Nat)
    (caller : RuntimeActivation) (scope : Nat) (allocationOrigin : OriginId) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id : Nat) (activation : RuntimeActivation)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before = .ok id allocated)
    (identifier : activation.act = allocated.nextAct) (channels : activation.channels = [.construct id])
    (ready : OpenDestinationBacking config.layout allocated id (.varr (.int .u8)) 0)
    (history : ReservationReferencesBounded before.construction ambient)
    (retainedBound : ∀ retained ∈ completedCarrierIds ambient.retained, retained < before.construction.destinations.size) :
    let pushed := { allocated with nextAct := allocated.nextAct + 1, activations := activation :: allocated.activations }
    let scopeState := ownershipResultScopeState activation scope pushed
    let prepared := { scopeState with construction := { scopeState.construction with
      exitReservations := scopeState.construction.exitReservations.push (.active .fresh id id ready.destination) } }
    AcceptedWorld config initialized prepared
      (.exitChannels [scopeState.construction.exitReservations.size] [] [.completed id] :: .callChannels activation [] :: ambient)
      types live (freshReceivingRegion before id :: regions) pending ∧
    prepared.objects = before.objects ∧ prepared.objectOrdinals = before.objectOrdinals := by
  obtain ⟨frame⟩ := newDestination_fresh_frame config.layout caller.act (.varr (.int .u8)) .value allocationOrigin knownCount
    before allocated id world.ownership.source.structural.1.1.1 created
  have freshId := newDestination_fresh_id config.layout caller.act (.varr (.int .u8)) .value allocationOrigin knownCount before allocated id created
  have newest : id + 1 = allocated.construction.destinations.size := by
    rw [frame.destinations, freshId]
    simp
  have allocatedHistory : ReservationReferencesBounded allocated.construction ambient := by
    simpa only [ReservationReferencesBounded, frame.tickets] using history
  have current := newDestination_current_self config initialized caller.act (.varr (.int .u8)) .value allocationOrigin
    knownCount before allocated id ambient types live regions pending world created
  have allocatedWorld := newDestination_acceptedWorld config caller.act (.varr (.int .u8)) .value allocationOrigin knownCount
    initialized before allocated id ambient types live regions pending world created
  have separated : ∀ retained ∈ completedCarrierIds ambient.retained,
      destinationDescendant allocated.construction.destinations id retained = false := by
    apply destination_retained_older_outside allocated.construction id ambient.retained
      allocatedWorld.ownership.source.structural.1.1.1.2.2.2
    intro retained member
    simpa only [freshId] using retainedBound retained member
  exact fresh_byte_call_prepared_world config initialized caller scope allocationOrigin knownCount before allocated id activation
    ambient types live regions pending world created identifier channels newest ready current allocatedHistory separated

theorem fresh_byte_call_prepared_world_from_history (config : EvalConfig) (initialized : Nat)
    (caller : RuntimeActivation) (scope : Nat) (allocationOrigin : OriginId) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id : Nat) (activation : RuntimeActivation)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before = .ok id allocated)
    (identifier : activation.act = allocated.nextAct) (channels : activation.channels = [.construct id])
    (history : ReservationReferencesBounded before.construction ambient)
    (retainedBound : ∀ retained ∈ completedCarrierIds ambient.retained, retained < before.construction.destinations.size) :
    ∃ ready : OpenDestinationBacking config.layout allocated id (.varr (.int .u8)) 0,
    let pushed := { allocated with nextAct := allocated.nextAct + 1, activations := activation :: allocated.activations }
    let scopeState := ownershipResultScopeState activation scope pushed
    let prepared := { scopeState with construction := { scopeState.construction with
      exitReservations := scopeState.construction.exitReservations.push (.active .fresh id id ready.destination) } }
    AcceptedWorld config initialized prepared
      (.exitChannels [scopeState.construction.exitReservations.size] [] [.completed id] :: .callChannels activation [] :: ambient)
      types live (freshReceivingRegion before id :: regions) pending ∧
    prepared.objects = before.objects ∧ prepared.objectOrdinals = before.objectOrdinals := by
  obtain ⟨ready⟩ := newDestination_initial_backing config.layout caller.act (.varr (.int .u8)) .value allocationOrigin
    knownCount before allocated id (.int .u8) rfl created
  exact ⟨ready, fresh_byte_call_prepared_world_bounded config initialized caller scope allocationOrigin knownCount before allocated id activation
    ambient types live regions pending world created identifier channels ready history retainedBound⟩

theorem fresh_byte_call_prepared_world_from_coverage (config : EvalConfig) (initialized : Nat)
    (caller : RuntimeActivation) (scope : Nat) (allocationOrigin : OriginId) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id : Nat) (activation : RuntimeActivation)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before = .ok id allocated)
    (identifier : activation.act = allocated.nextAct) (channels : activation.channels = [.construct id])
    (history : ReservationReferencesBounded before.construction ambient)
    (coverage : EvaluationHistoryCoverage before ambient pending) :
    ∃ ready : OpenDestinationBacking config.layout allocated id (.varr (.int .u8)) 0,
    let pushed := { allocated with nextAct := allocated.nextAct + 1, activations := activation :: allocated.activations }
    let scopeState := ownershipResultScopeState activation scope pushed
    let prepared := { scopeState with construction := { scopeState.construction with
      exitReservations := scopeState.construction.exitReservations.push (.active .fresh id id ready.destination) } }
    AcceptedWorld config initialized prepared
      (.exitChannels [scopeState.construction.exitReservations.size] [] [.completed id] :: .callChannels activation [] :: ambient)
      types live (freshReceivingRegion before id :: regions) pending ∧
    prepared.objects = before.objects ∧ prepared.objectOrdinals = before.objectOrdinals := by
  exact fresh_byte_call_prepared_world_from_history config initialized caller scope allocationOrigin knownCount before allocated id activation
    ambient types live regions pending world created identifier channels history
    (retained_destination_bounds config initialized before ambient types live regions pending world coverage)

theorem fresh_byte_call_actual_prepared_world (config : EvalConfig) (initialized : Nat)
    (caller : RuntimeActivation) (scope : Nat) (allocationOrigin : OriginId) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id implId : Nat) (helper : Impl)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before = .ok id allocated)
    (coverage : EvaluationHistoryCoverage before ambient pending) :
    let activation : RuntimeActivation := ⟨implId, allocated.nextAct, helper.vars, [], [.construct id]⟩
    ∃ ready : OpenDestinationBacking config.layout allocated id (.varr (.int .u8)) 0,
    let pushed := { allocated with nextAct := allocated.nextAct + 1, activations := activation :: allocated.activations }
    let scopeState := ownershipResultScopeState activation scope pushed
    let prepared := { scopeState with construction := { scopeState.construction with
      exitReservations := scopeState.construction.exitReservations.push (.active .fresh id id ready.destination) } }
    AcceptedWorld config initialized prepared
      (.exitChannels [scopeState.construction.exitReservations.size] [] [.completed id] :: .callChannels activation [] :: ambient)
      types live (freshReceivingRegion before id :: regions) pending ∧
    prepared.objects = before.objects ∧ prepared.objectOrdinals = before.objectOrdinals := by
  exact fresh_byte_call_prepared_world_from_coverage config initialized caller scope allocationOrigin knownCount before allocated id
    ⟨implId, allocated.nextAct, helper.vars, [], [.construct id]⟩ ambient types live regions pending world created rfl rfl coverage.1 coverage

#print axioms fresh_byte_call_actual_prepared_world
#print axioms fresh_byte_call_prepared_world_from_coverage
#print axioms fresh_byte_call_prepared_world_from_history
#print axioms fresh_byte_call_prepared_world_bounded
#print axioms fresh_byte_call_prepared_world
end Goose.Proofs.ConstructionAcceptedExecution
