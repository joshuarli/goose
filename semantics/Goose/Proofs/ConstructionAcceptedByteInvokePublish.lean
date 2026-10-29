import Goose.Proofs.ConstructionAcceptedFreshByteInvoke
import Goose.Proofs.ConstructionAcceptedBytePublishWorld
import Goose.Proofs.ConstructionAcceptedByteScopeObservations

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem fresh_byteInvoke_publish_bounded (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (caller : RuntimeActivation) (contextId scope : Nat) (bytes : List UInt8)
    (allocationOrigin origin : OriginId) (context : Context) (helper : Impl) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id : Nat) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (world : AcceptedWorld config frame.initialized before ambient types live [] [])
    (source : AcceptedFrame config accepted frame before types)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[])
    (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩])
    (body : helper.body = ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩)
    (absent : ∀ descriptor ∈ helper.vars.toList, descriptor.scope ≠ scope)
    (history : ReservationReferencesBounded before.construction ambient)
    (retainedBound : ∀ retained ∈ completedCarrierIds ambient.retained, retained < before.construction.destinations.size)
    (fits : bytes.length < 2 ^ 32) (depth : before.activations.length < Goose.Core.maxCallDepth)
    (created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before = .ok id allocated) :
    let outcome := (do
      let carriers ← invokeCall fuel config caller contextId [] [.construct id] origin
      publishCarriers allocationOrigin carriers
      pure carriers) allocated
    match outcome with
    | .stop _ after => ∃ nextAmbient, AcceptedWorld config frame.initialized after nextAmbient types live [freshReceivingRegion before id] []
    | .ok carriers after => ∃ stored, carriers = [.completed id] ∧
        AcceptedWorld config frame.initialized after ambient types live [] [] ∧
        AcceptedFrame config accepted frame after types ∧
        storedDestination id after = .ok stored after ∧ StoredValueBacking config.layout after stored ∧
        stored.storage = before.construction.storage.size ∧ stored.destination = some id ∧ stored.ty = .varr (.int .u8)
    | _ => False := by
  have observed := fresh_byteInvoke_bounded fuel config frame.initialized caller contextId scope bytes allocationOrigin origin context helper
    knownCount before allocated id ambient types live world contextAt helperAt parameters results body absent history retainedBound fits depth created
  cases invoked : invokeCall fuel config caller contextId [] [.construct id] origin allocated with
  | escape target carriers after | jump target kind after => simp [invoked] at observed
  | stop reason after =>
    simp only [invoked] at observed
    simp only [invoked, bind]
    exact observed
  | ok carriers returned =>
    simp only [invoked] at observed
    obtain ⟨same, returnedWorld, objects, ordinals, acts, scopes, ⟨facts⟩⟩ := observed
    subst carriers
    obtain ⟨published, publishedEq⟩ := publish_direct_packed_success allocationOrigin returned id before.construction.storage.size bytes.length
      facts.row facts.storage facts.present facts.stored facts.progress facts.receiver facts.backing facts.storageEq facts.packed facts.adaptation fits
    have isolation := acceptedWorld_freshStorage_unreferenced_after config frame.initialized before returned ambient types live [] [] world objects
    let region := freshReceivingRegion before id
    have mutable : id ∈ region.mutableDestinations := by simp [region, freshReceivingRegion]
    have outside : ∀ root, live root → ¬ region.mutableRoots root := by simp [region, freshReceivingRegion]
    have finalWorld := returnedWorld.publish_direct_packed_general config frame.initialized allocationOrigin returned published ambient types live
      region id before.construction.storage.size bytes.length facts.row facts.storage mutable outside isolation
      facts.present facts.stored facts.progress facts.receiver facts.backing facts.packed publishedEq
    obtain ⟨outer, destinations, storages, successors, tickets⟩ := publish_direct_packed_observed allocationOrigin returned published
      id before.construction.storage.size bytes.length facts.row facts.storage facts.present facts.stored facts.progress facts.receiver facts.backing facts.packed publishedEq
    have finalObjects : published.objects = before.objects := by
      simpa only using (congrArg ExecutionState.objects outer).trans objects
    have finalOrdinals : published.objectOrdinals = before.objectOrdinals := by
      simpa only using (congrArg ExecutionState.objectOrdinals outer).trans ordinals
    have finalActs : before.nextAct ≤ published.nextAct := by
      have same : published.nextAct = before.nextAct + 1 := by simpa only using (congrArg ExecutionState.nextAct outer).trans acts
      omega
    have finalScopes : before.nextScope ≤ published.nextScope := by
      have same : published.nextScope = before.nextScope + 1 := by simpa only using (congrArg ExecutionState.nextScope outer).trans scopes
      omega
    have finalFrame := source.after_monotone_unchanged_objects finalObjects finalOrdinals finalActs finalScopes
    have sampled : SampledRunBacking config.layout facts.storage.bytes
        ⟨facts.row.capability.start + (if facts.row.layout == .packed && facts.row.capability.request == .value then 4 else 0),
          bytes.length, .int .u8⟩ := by simpa [facts.packed, facts.request] using facts.sampled
    obtain ⟨value, sampledValue, backed, storageEq, destinationEq, typeEq⟩ :=
      publish_direct_packed_backing config.layout allocationOrigin id before.construction.storage.size bytes.length returned published
        facts.row facts.storage facts.present facts.stored facts.backing facts.progress facts.receiver facts.packed sampled facts.logical publishedEq
    simp only [invoked, bind, publishedEq, pure]
    exact ⟨value, trivial, finalWorld, finalFrame, sampledValue, backed, storageEq, destinationEq, typeEq⟩

theorem fresh_byteInvoke_publish_ticketed (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (caller : RuntimeActivation) (contextId scope : Nat) (bytes : List UInt8)
    (allocationOrigin origin : OriginId) (context : Context) (helper : Impl) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id : Nat) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
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
    (fits : bytes.length < 2 ^ 32) (depth : before.activations.length < Goose.Core.maxCallDepth)
    (created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before = .ok id allocated) :
    let outcome := (do
      let carriers ← invokeCall fuel config caller contextId [] [.construct id] origin
      publishCarriers allocationOrigin carriers
      pure carriers) allocated
    match outcome with
    | .stop _ after => ∃ nextAmbient, AcceptedWorld config frame.initialized after nextAmbient types live [freshReceivingRegion before id] []
    | .ok carriers after => ∃ stored, carriers = [.completed id] ∧
        AcceptedWorld config frame.initialized after ambient types live [] [] ∧
        AcceptedFrame config accepted frame after types ∧
        storedDestination id after = .ok stored after ∧ StoredValueBacking config.layout after stored ∧
        stored.storage = before.construction.storage.size ∧ stored.destination = some id ∧ stored.ty = .varr (.int .u8)
    | _ => False := by
  apply fresh_byteInvoke_publish_bounded fuel config accepted frame caller contextId scope bytes allocationOrigin origin context helper
    knownCount before allocated id ambient types live world source contextAt helperAt parameters results body absent history ?_ fits depth created
  intro retained member
  rw [noRetained] at member
  cases member

theorem fresh_byteInvoke_publish_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (caller : RuntimeActivation) (contextId scope : Nat) (bytes : List UInt8)
    (allocationOrigin origin : OriginId) (context : Context) (helper : Impl) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id : Nat) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
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
    (noTickets : ∀ ambientFrame ∈ ambient, ambientFrame.tickets = [])
    (fits : bytes.length < 2 ^ 32) (depth : before.activations.length < Goose.Core.maxCallDepth)
    (created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before = .ok id allocated) :
    let outcome := (do
      let carriers ← invokeCall fuel config caller contextId [] [.construct id] origin
      publishCarriers allocationOrigin carriers
      pure carriers) allocated
    match outcome with
    | .stop _ after => ∃ nextAmbient, AcceptedWorld config frame.initialized after nextAmbient types live [freshReceivingRegion before id] []
    | .ok carriers after => ∃ stored, carriers = [.completed id] ∧
        AcceptedWorld config frame.initialized after ambient types live [] [] ∧
        AcceptedFrame config accepted frame after types ∧
        storedDestination id after = .ok stored after ∧ StoredValueBacking config.layout after stored ∧
        stored.storage = before.construction.storage.size ∧ stored.destination = some id ∧ stored.ty = .varr (.int .u8)
    | _ => False := by
  exact fresh_byteInvoke_publish_ticketed fuel config accepted frame caller contextId scope bytes allocationOrigin origin context helper
    knownCount before allocated id ambient types live world source contextAt helperAt parameters results body absent history noRetained fits depth created

#print axioms fresh_byteInvoke_publish_bounded
#print axioms fresh_byteInvoke_publish_ticketed
#print axioms fresh_byteInvoke_publish_world
end Goose.Proofs.ConstructionAcceptedExecution
