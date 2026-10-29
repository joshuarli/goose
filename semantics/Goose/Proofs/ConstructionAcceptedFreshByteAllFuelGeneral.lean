import Goose.Proofs.ConstructionAcceptedFreshByteInvokeGeneral
import Goose.Proofs.ConstructionAcceptedByteInvokeTimeout

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem fresh_byteInvoke_pending_allFuel (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (caller : RuntimeActivation) (contextId scope : Nat) (bytes : List UInt8) (allocationOrigin origin : OriginId)
    (context : Context) (helper : Impl) (knownCount : Option Nat) (before allocated : ExecutionState) (id : Nat)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (coverage : EvaluationHistoryCoverage before ambient pending)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[])
    (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩])
    (body : helper.body = ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩)
    (absent : ∀ descriptor ∈ helper.vars.toList, descriptor.scope ≠ scope)
    (fits : bytes.length < 2 ^ 32) (depth : before.activations.length < Goose.Core.maxCallDepth)
    (created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before = .ok id allocated) :
    match invokeCall fuel config caller contextId [] [.construct id] origin allocated with
    | .stop _ after => ∃ nextAmbient, AcceptedWorld config initialized after nextAmbient types live (freshReceivingRegion before id :: regions) pending
    | .ok carriers after => carriers = [.completed id] ∧
        AcceptedWorld config initialized after (.returned carriers :: ambient) types live (freshReceivingRegion before id :: regions)
          (⟨[.construct id], carriers⟩ :: pending) ∧
        after.objects = before.objects ∧ after.objectOrdinals = before.objectOrdinals ∧
        after.nextAct = before.nextAct + 1 ∧ after.nextScope = before.nextScope + 1 ∧
        Nonempty (BuiltByteReceiver config.layout after id before.construction.storage.size bytes.length)
    | _ => False := by
  obtain ⟨ready⟩ := newDestination_initial_backing config.layout caller.act (.varr (.int .u8)) .value allocationOrigin
    knownCount before allocated id (.int .u8) rfl created
  obtain ⟨destination, found, packed, request, backing, receiver, adaptation, physical⟩ :=
    newDestination_byteOwner_packed_value_with_physical config.layout caller.act allocationOrigin knownCount before allocated id created
  have same : destination = ready.destination := Option.some.inj (found.symm.trans ready.present)
  subst destination
  have allocatedWorld := newDestination_acceptedWorld config caller.act (.varr (.int .u8)) .value allocationOrigin knownCount
    initialized before allocated id ambient types live regions pending world created
  obtain ⟨freshFrame⟩ := newDestination_fresh_frame config.layout caller.act (.varr (.int .u8)) .value allocationOrigin knownCount
    before allocated id world.ownership.source.structural.1.1.1 created
  have allocatedHistory : ReservationReferencesBounded allocated.construction ambient := by
    simpa only [ReservationReferencesBounded, freshFrame.tickets] using coverage.1
  have current := newDestination_current_self config initialized caller.act (.varr (.int .u8)) .value allocationOrigin
    knownCount before allocated id ambient types live regions pending world created
  have allocatedDepth : allocated.activations.length < Goose.Core.maxCallDepth := by
    have sameActs := congrArg ExecutionState.activations freshFrame.outer
    simpa only [sameActs] using depth
  have freshId := newDestination_fresh_id config.layout caller.act (.varr (.int .u8)) .value allocationOrigin knownCount before allocated id created
  have newest : id + 1 = allocated.construction.destinations.size := by
    rw [freshFrame.destinations, freshId]
    simp
  have within : ∀ receiving, destinationCurrent allocated.construction id = .ok receiving →
      OwnershipReceivingWithinSuccessorFrames allocated.construction ambient receiving := by
    intro receiving resolved
    have same : receiving = id := Except.ok.inj (resolved.symm.trans current)
    subst receiving
    exact newest_destination_within_successorFrames allocated.construction ambient id newest
      allocatedWorld.ownership.source.structural.1.1.1.2.2.2
  have separated : ∀ retained ∈ completedCarrierIds ambient.retained,
      destinationDescendant allocated.construction.destinations id retained = false := by
    apply destination_retained_older_outside allocated.construction id ambient.retained
      allocatedWorld.ownership.source.structural.1.1.1.2.2.2
    intro retained member
    simpa only [freshId] using retained_destination_bounds config initialized before ambient types live regions pending world coverage retained member
  have low := invokeByteReceiver_lowFuel_pending config initialized caller contextId id scope bytes origin context helper allocated ambient
    types live (freshReceivingRegion before id :: regions) pending allocatedWorld contextAt helperAt parameters results body allocatedHistory separated within
    ready receiver current allocatedDepth
  cases fuel with
  | zero => simpa only [low.1] using ⟨ambient, allocatedWorld⟩
  | succ fuel =>
    cases fuel with
    | zero => simpa only [low.2.1] using ⟨ambient, allocatedWorld⟩
    | succ fuel =>
      cases fuel with
      | zero => simpa only [low.2.2.1] using ⟨_, low.2.2.2.2.2.1⟩
      | succ fuel =>
        cases fuel with
        | zero => simpa only [low.2.2.2.1] using ⟨_, low.2.2.2.2.2.2.1⟩
        | succ fuel =>
          cases fuel with
          | zero => simpa only [low.2.2.2.2.1] using ⟨_, low.2.2.2.2.2.2.2⟩
          | succ fuel =>
            obtain ⟨after, executed, finalWorld, objects, ordinals, acts, scopes, geometry⟩ :=
              fresh_byte_call_invoke_world fuel config initialized caller contextId scope allocationOrigin origin knownCount
                before allocated id context helper bytes ambient types live regions pending world coverage created
                contextAt helperAt parameters results body absent ready fits depth
            simp only [executed]
            exact ⟨trivial, finalWorld, objects, ordinals, acts, scopes, geometry⟩

#print axioms fresh_byteInvoke_pending_allFuel
end Goose.Proofs.ConstructionAcceptedExecution
