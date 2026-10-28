import Goose.Proofs.ConstructionAcceptedByteInvokeTimeout
import Goose.Proofs.ConstructionAcceptedFreshByteCompletion
import Goose.Proofs.ConstructionAcceptedByteAllocationOutcome

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem fresh_byteInvoke_observed (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (caller : RuntimeActivation) (contextId scope : Nat) (bytes : List UInt8) (allocationOrigin origin : OriginId)
    (context : Context) (helper : Impl) (knownCount : Option Nat) (before allocated : ExecutionState) (id : Nat)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (world : AcceptedWorld config initialized before ambient types live [] [])
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[])
    (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩])
    (body : helper.body = ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩)
    (absent : ∀ descriptor ∈ helper.vars.toList, descriptor.scope ≠ scope)
    (history : ReservationReferencesBounded before.construction ambient)
    (noRetained : completedCarrierIds ambient.retained = [])
    (noTickets : ∀ frame ∈ ambient, frame.tickets = [])
    (fits : bytes.length < 2 ^ 32) (depth : before.activations.length < Goose.Core.maxCallDepth)
    (created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before = .ok id allocated) :
    match invokeCall fuel config caller contextId [] [.construct id] origin allocated with
    | .stop _ after => ∃ nextAmbient, AcceptedWorld config initialized after nextAmbient types live [freshReceivingRegion before id] []
    | .ok carriers after => carriers = [.completed id] ∧
        AcceptedWorld config initialized after (.returned carriers :: ambient) types live [freshReceivingRegion before id]
          [⟨[.construct id], carriers⟩] ∧
        after.objects = before.objects ∧ after.objectOrdinals = before.objectOrdinals ∧
        after.nextAct = before.nextAct + 1 ∧ after.nextScope = before.nextScope + 1
    | _ => False := by
  obtain ⟨ready⟩ := newDestination_initial_backing config.layout caller.act (.varr (.int .u8)) .value allocationOrigin
    knownCount before allocated id (.int .u8) rfl created
  obtain ⟨destination, found, packed, request, backing, receiver, adaptation, physical⟩ :=
    newDestination_byteOwner_packed_value_with_physical config.layout caller.act allocationOrigin knownCount before allocated id created
  have same : destination = ready.destination := Option.some.inj (found.symm.trans ready.present)
  subst destination
  have allocatedWorld := newDestination_acceptedWorld config caller.act (.varr (.int .u8)) .value allocationOrigin knownCount
    initialized before allocated id ambient types live [] [] world created
  obtain ⟨freshFrame⟩ := newDestination_fresh_frame config.layout caller.act (.varr (.int .u8)) .value allocationOrigin knownCount
    before allocated id world.ownership.source.structural.1.1.1 created
  have allocatedHistory : ReservationReferencesBounded allocated.construction ambient := by
    simpa only [ReservationReferencesBounded, freshFrame.tickets] using history
  have current := newDestination_current_self config initialized caller.act (.varr (.int .u8)) .value allocationOrigin
    knownCount before allocated id ambient types live [] [] world created
  obtain ⟨freshRow, freshFound, freshStorage, afterSize⟩ :=
    newDestination_success_fresh config.layout caller.act (.varr (.int .u8)) .value allocationOrigin knownCount before allocated id created
  have sameRow : freshRow = ready.destination := Option.some.inj (freshFound.symm.trans ready.present)
  have extent : storageExtent before ready.destination.storage = 0 := by
    have bound : before.construction.storage.size ≤ ready.destination.storage := by simpa only [sameRow] using afterSize
    simp [storageExtent, Array.getElem?_eq_none_iff.mpr bound]
  have mutable : ∀ region ∈ [freshReceivingRegion before id], id ∈ region.mutableDestinations := by
    intro region member
    simp only [List.mem_singleton] at member
    subst region
    simp [freshReceivingRegion]
  have cutoff : ∀ region ∈ [freshReceivingRegion before id],
      region.limit ready.destination.storage ≤ ready.destination.capability.start := by
    intro region member
    simp only [List.mem_singleton] at member
    subst region
    simp [freshReceivingRegion, extent]
  have covered : ∀ root, live root → ∃ region ∈ [freshReceivingRegion before id], ¬ region.mutableRoots root := by
    intro root active
    exact ⟨freshReceivingRegion before id, by simp, by simp [freshReceivingRegion]⟩
  have allocatedDepth : allocated.activations.length < Goose.Core.maxCallDepth := by
    have sameActs := congrArg ExecutionState.activations freshFrame.outer
    simpa only [sameActs] using depth
  have low := invokeByteReceiver_lowFuel_world config initialized caller contextId id scope bytes origin context helper allocated ambient
    types live [freshReceivingRegion before id] allocatedWorld contextAt helperAt parameters results body allocatedHistory noRetained noTickets
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
            obtain ⟨after, executed, finalWorld, objects, ordinals, acts, scopes⟩ := invokeByteReceiver_success_observed fuel config initialized caller contextId id scope bytes origin
              context helper allocated ambient types live [freshReceivingRegion before id] allocatedWorld contextAt helperAt parameters results body absent
              allocatedHistory noRetained noTickets ready packed adaptation receiver request physical current fits mutable cutoff covered allocatedDepth
            have outerObjects : allocated.objects = before.objects := by simpa only using congrArg ExecutionState.objects freshFrame.outer
            have outerOrdinals : allocated.objectOrdinals = before.objectOrdinals := by simpa only using congrArg ExecutionState.objectOrdinals freshFrame.outer
            have outerActs : allocated.nextAct = before.nextAct := by simpa only using congrArg ExecutionState.nextAct freshFrame.outer
            have outerScopes : allocated.nextScope = before.nextScope := by simpa only using congrArg ExecutionState.nextScope freshFrame.outer
            simp only [executed]
            exact ⟨trivial, finalWorld, objects.trans outerObjects, ordinals.trans outerOrdinals,
              by simpa only [outerActs] using acts, by simpa only [outerScopes] using scopes⟩

theorem fresh_byteInvoke_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (caller : RuntimeActivation) (contextId scope : Nat) (bytes : List UInt8) (allocationOrigin origin : OriginId)
    (context : Context) (helper : Impl) (knownCount : Option Nat) (before allocated : ExecutionState) (id : Nat)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (world : AcceptedWorld config initialized before ambient types live [] [])
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[])
    (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩])
    (body : helper.body = ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩)
    (absent : ∀ descriptor ∈ helper.vars.toList, descriptor.scope ≠ scope)
    (history : ReservationReferencesBounded before.construction ambient)
    (noRetained : completedCarrierIds ambient.retained = [])
    (noTickets : ∀ frame ∈ ambient, frame.tickets = [])
    (fits : bytes.length < 2 ^ 32) (depth : before.activations.length < Goose.Core.maxCallDepth)
    (created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before = .ok id allocated) :
    match invokeCall fuel config caller contextId [] [.construct id] origin allocated with
    | .stop _ after => ∃ nextAmbient, AcceptedWorld config initialized after nextAmbient types live [freshReceivingRegion before id] []
    | .ok carriers after => carriers = [.completed id] ∧
        AcceptedWorld config initialized after (.returned carriers :: ambient) types live [freshReceivingRegion before id]
          [⟨[.construct id], carriers⟩]
    | _ => False := by
  have observed := fresh_byteInvoke_observed fuel config initialized caller contextId scope bytes allocationOrigin origin context helper
    knownCount before allocated id ambient types live world contextAt helperAt parameters results body absent history noRetained noTickets fits depth created
  cases outcome : invokeCall fuel config caller contextId [] [.construct id] origin allocated with
  | ok carriers after =>
    simp only [outcome] at observed ⊢
    exact ⟨observed.1, observed.2.1⟩
  | stop reason after => simpa only [outcome] using observed
  | escape target carriers after => simp only [outcome] at observed
  | jump target kind after => simp only [outcome] at observed

theorem allocate_then_invoke_byte_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (caller : RuntimeActivation) (contextId scope : Nat) (bytes : List UInt8)
    (allocationOrigin origin : OriginId) (context : Context) (helper : Impl) (knownCount : Option Nat)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (world : AcceptedWorld config frame.initialized before ambient types live [] [])
    (source : AcceptedFrame config accepted frame before types)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[])
    (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩])
    (body : helper.body = ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩)
    (absent : ∀ descriptor ∈ helper.vars.toList, descriptor.scope ≠ scope)
    (history : ReservationReferencesBounded before.construction ambient)
    (noRetained : completedCarrierIds ambient.retained = [])
    (noTickets : ∀ frame ∈ ambient, frame.tickets = [])
    (fits : bytes.length < 2 ^ 32) (depth : before.activations.length < Goose.Core.maxCallDepth) :
    let outcome := (do
      let id ← newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount
      invokeCall fuel config caller contextId [] [.construct id] origin) before
    match outcome with
    | .stop _ after => ∃ nextAmbient nextRegions,
        AcceptedWorld config frame.initialized after nextAmbient types live nextRegions []
    | .ok carriers after => ∃ id, carriers = [.completed id] ∧
        AcceptedWorld config frame.initialized after (.returned carriers :: ambient) types live [freshReceivingRegion before id]
          [⟨[.construct id], carriers⟩]
    | _ => False := by
  have allocation := newDestination_byteOwner_world_outcome config accepted frame caller.act allocationOrigin knownCount
    before ambient types live [] [] world source
  cases created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before with
  | escape address carriers after | jump target kind after => simp [created] at allocation
  | stop reason after =>
    simp only [created] at allocation
    simp only [created, bind]
    exact ⟨ambient, [], allocation.1⟩
  | ok id allocated =>
    have invoked := fresh_byteInvoke_world fuel config frame.initialized caller contextId scope bytes allocationOrigin origin context helper
      knownCount before allocated id ambient types live world contextAt helperAt parameters results body absent history noRetained noTickets fits depth created
    cases finished : invokeCall fuel config caller contextId [] [.construct id] origin allocated with
    | escape address carriers after | jump target kind after => simp [finished] at invoked
    | stop reason after =>
      simp only [finished] at invoked
      simp only [created, bind, finished]
      obtain ⟨nextAmbient, finalWorld⟩ := invoked
      exact ⟨nextAmbient, [freshReceivingRegion before id], finalWorld⟩
    | ok carriers after =>
      simp only [finished] at invoked
      obtain ⟨same, finalWorld⟩ := invoked
      simp only [created, bind, finished]
      exact ⟨id, same, finalWorld⟩

#print axioms allocate_then_invoke_byte_world
#print axioms fresh_byteInvoke_observed
#print axioms fresh_byteInvoke_world
end Goose.Proofs.ConstructionAcceptedExecution
