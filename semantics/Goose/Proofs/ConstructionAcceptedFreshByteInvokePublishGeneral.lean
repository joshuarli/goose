import Goose.Proofs.ConstructionAcceptedFreshBytePublishWorld
import Goose.Proofs.ConstructionAcceptedByteInvokePublish

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem fresh_byteInvoke_publish_frame_allFuel (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (caller : RuntimeActivation) (contextId scope : Nat) (bytes : List UInt8)
    (allocationOrigin origin : OriginId) (context : Context) (helper : Impl) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id : Nat) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (coverage : EvaluationHistoryCoverage before ambient pending)
    (source : AcceptedFrame config accepted frame before types)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[])
    (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩])
    (body : helper.body = ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩)
    (absent : ∀ descriptor ∈ helper.vars.toList, descriptor.scope ≠ scope)
    (fits : bytes.length < 2 ^ 32) (depth : before.activations.length < Goose.Core.maxCallDepth)
    (created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before = .ok id allocated) :
    let outcome := (do
      let carriers ← invokeCall fuel config caller contextId [] [.construct id] origin
      publishCarriers allocationOrigin carriers
      pure carriers) allocated
    match outcome with
    | .stop _ after => ∃ nextAmbient, AcceptedWorld config frame.initialized after nextAmbient types live (freshReceivingRegion before id :: regions) pending
    | .ok carriers after => ∃ stored, carriers = [.completed id] ∧
        AcceptedWorld config frame.initialized after ambient types live regions pending ∧
        AcceptedFrame config accepted frame after types ∧
        storedDestination id after = .ok stored after ∧ StoredValueBacking config.layout after stored ∧
        stored.storage = before.construction.storage.size ∧ stored.destination = some id ∧ stored.ty = .varr (.int .u8) ∧
        after.objectOrdinals = before.objectOrdinals ∧ before.nextAct ≤ after.nextAct ∧ before.nextScope ≤ after.nextScope ∧
        Nonempty (FreshDestinationFrame { after with construction := { before.construction with
          exitReservations := before.construction.exitReservations.push .released } } after)
    | _ => False := by
  have observed := fresh_byteInvoke_pending_frame_allFuel fuel config frame.initialized caller contextId scope bytes allocationOrigin origin context helper
    knownCount before allocated id ambient types live regions pending world coverage contextAt helperAt parameters results body absent fits depth created
  cases invoked : invokeCall fuel config caller contextId [] [.construct id] origin allocated with
  | escape target carriers after | jump target kind after => simp [invoked] at observed
  | stop reason after =>
    simp only [invoked] at observed
    simp only [invoked, bind]
    exact observed
  | ok carriers returned =>
    simp only [invoked] at observed
    obtain ⟨same, returnedWorld, objects, ordinals, acts, scopes, ⟨facts⟩, ⟨freshFrame⟩⟩ := observed
    subst carriers
    obtain ⟨published, publishedEq⟩ := publish_direct_packed_success allocationOrigin returned id before.construction.storage.size bytes.length
      facts.row facts.storage facts.present facts.stored facts.progress facts.receiver facts.backing facts.storageEq facts.packed facts.adaptation fits
    have isolation := acceptedWorld_freshStorage_unreferenced_after config frame.initialized before returned ambient types live regions pending world objects
    have freshId := newDestination_fresh_id config.layout caller.act (.varr (.int .u8)) .value allocationOrigin knownCount before allocated id created
    obtain ⟨publishedFrame, _⟩ := fresh_byte_publish_frame_pending config frame.initialized allocationOrigin before returned published
      ambient types live regions pending id bytes.length facts.row world freshId freshFrame facts.present facts.backing facts.progress facts.packed publishedEq
    have finalWorld := fresh_byte_publish_accepted_world config frame.initialized allocationOrigin returned published ambient before
      types live regions pending id before.construction.storage.size bytes.length facts.row facts.storage world returnedWorld freshId rfl freshFrame isolation
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
    exact ⟨value, trivial, finalWorld, finalFrame, sampledValue, backed, storageEq, destinationEq, typeEq, finalOrdinals, finalActs, finalScopes, publishedFrame⟩

theorem fresh_byteInvoke_publish_pending_allFuel (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (caller : RuntimeActivation) (contextId scope : Nat) (bytes : List UInt8)
    (allocationOrigin origin : OriginId) (context : Context) (helper : Impl) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id : Nat) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (coverage : EvaluationHistoryCoverage before ambient pending)
    (source : AcceptedFrame config accepted frame before types)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[])
    (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩])
    (body : helper.body = ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩)
    (absent : ∀ descriptor ∈ helper.vars.toList, descriptor.scope ≠ scope)
    (fits : bytes.length < 2 ^ 32) (depth : before.activations.length < Goose.Core.maxCallDepth)
    (created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before = .ok id allocated) :
    let outcome := (do
      let carriers ← invokeCall fuel config caller contextId [] [.construct id] origin
      publishCarriers allocationOrigin carriers
      pure carriers) allocated
    match outcome with
    | .stop _ after => ∃ nextAmbient, AcceptedWorld config frame.initialized after nextAmbient types live (freshReceivingRegion before id :: regions) pending
    | .ok carriers after => ∃ stored, carriers = [.completed id] ∧
        AcceptedWorld config frame.initialized after ambient types live regions pending ∧
        AcceptedFrame config accepted frame after types ∧
        storedDestination id after = .ok stored after ∧ StoredValueBacking config.layout after stored ∧
        stored.storage = before.construction.storage.size ∧ stored.destination = some id ∧ stored.ty = .varr (.int .u8)
    | _ => False := by
  have outcome := fresh_byteInvoke_publish_frame_allFuel fuel config accepted frame caller contextId scope bytes allocationOrigin origin context helper
    knownCount before allocated id ambient types live regions pending world coverage source contextAt helperAt parameters results body absent fits depth created
  cases result : (do
      let carriers ← invokeCall fuel config caller contextId [] [.construct id] origin
      publishCarriers allocationOrigin carriers
      pure carriers) allocated with
  | stop reason after => simpa only [result] using outcome
  | ok carriers after =>
    simp only [result] at outcome ⊢
    obtain ⟨stored, same, finalWorld, finalFrame, sampled, backed, storageEq, destinationEq, typeEq, ordinals, acts, scopes, frame⟩ := outcome
    exact ⟨stored, same, finalWorld, finalFrame, sampled, backed, storageEq, destinationEq, typeEq⟩
  | escape target carriers after => simpa only [result] using outcome
  | jump target kind after => simpa only [result] using outcome

#print axioms fresh_byteInvoke_publish_frame_allFuel
#print axioms fresh_byteInvoke_publish_pending_allFuel
end Goose.Proofs.ConstructionAcceptedExecution
