import Goose.Proofs.ConstructionAcceptedFreshByteCompletionCall
import Goose.Proofs.ConstructionAcceptedByteBodyFinish
import Goose.Proofs.ConstructionAcceptedByteInvokeEquation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem fresh_byte_call_invoke_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (caller : RuntimeActivation) (contextId scope : Nat) (allocationOrigin origin : OriginId) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id : Nat) (context : Context) (helper : Impl) (bytes : List UInt8)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (coverage : EvaluationHistoryCoverage before ambient pending)
    (created : newDestination config.layout caller.act (.varr (.int .u8)) .value allocationOrigin none knownCount before = .ok id allocated)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[])
    (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩])
    (body : helper.body = ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩)
    (absent : ∀ descriptor ∈ helper.vars.toList, descriptor.scope ≠ scope)
    (ready : OpenDestinationBacking config.layout allocated id (.varr (.int .u8)) 0)
    (fits : bytes.length < 2 ^ 32) (depth : before.activations.length < Goose.Core.maxCallDepth) :
    ∃ after, invokeCall (fuel + 5) config caller contextId [] [.construct id] origin allocated = .ok [.completed id] after ∧
      AcceptedWorld config initialized after (.returned [.completed id] :: ambient) types live
        (freshReceivingRegion before id :: regions) (⟨[.construct id], [.completed id]⟩ :: pending) ∧
      after.objects = before.objects ∧ after.objectOrdinals = before.objectOrdinals ∧
      after.nextAct = before.nextAct + 1 ∧ after.nextScope = before.nextScope + 1 ∧
      Nonempty (BuiltByteReceiver config.layout after id before.construction.storage.size bytes.length) := by
  let activation : RuntimeActivation := ⟨context.impl, allocated.nextAct, helper.vars, [], [.construct id]⟩
  let pushed := { allocated with nextAct := allocated.nextAct + 1, activations := activation :: allocated.activations }
  let scopeState := ownershipResultScopeState activation scope pushed
  obtain ⟨built, produced, builtWorld, outer, ⟨normalized⟩, ⟨geometry⟩⟩ :=
    fresh_byte_call_completion_observed_world fuel config initialized caller scope allocationOrigin origin knownCount
      before allocated id context.impl helper bytes ambient types live regions pending world coverage created ready fits
  let released := releaseScopeState activation scope pushed.nextScope built
  have releasedWorld := builtWorld.releaseScope_withoutDeclarations config initialized built
    (.returned [.completed id] :: .callChannels activation [] :: ambient) types live (freshReceivingRegion before id :: regions)
    (⟨[.construct id], [.completed id]⟩ :: pending) activation scope pushed.nextScope absent
  have releasedValid : NormalizedCompletedCarrier released (.varr (.int .u8)) id :=
    NormalizedCompletedCarrier.of_construction_eq (before := built) (after := released) rfl normalized
  have bound : bindAll activation.act pushed.nextScope [] scopeState = .ok () scopeState := by simp [bindAll, bind, pure]
  have normal : execStmts (fuel + 2) config { activation with scopes := (scope, pushed.nextScope) :: activation.scopes }
      [] scopeState = .ok (.normal .unit) scopeState := by simp [execStmts, pure]
  have bodyDone := execActivationBody_bound_channelTail (fuel + 2) config activation [] scope []
    (.bytes (.varr (.int .u8)) bytes origin) pushed scopeState scopeState bound normal
  have done : execActivationBody (fuel + 3) config activation [] ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩ pushed =
      .ok [.completed id] released := by
    simp only [activation, expressionOrigin] at bodyDone
    rw [produced] at bodyDone
    simpa [released, Nat.add_assoc] using bodyDone
  obtain ⟨finish, finalWorld⟩ := finishConstructSelfCall_world (fuel + 4) config initialized activation id (.varr (.int .u8)) origin
    _ pushed released ambient types live (freshReceivingRegion before id :: regions) (⟨[.construct id], [.completed id]⟩ :: pending)
    rfl done releasedWorld releasedValid
  obtain ⟨frame⟩ := newDestination_fresh_frame config.layout caller.act (.varr (.int .u8)) .value allocationOrigin knownCount
    before allocated id world.ownership.source.structural.1.1.1 created
  have current := newDestination_current_self config initialized caller.act (.varr (.int .u8)) .value allocationOrigin
    knownCount before allocated id ambient types live regions pending world created
  obtain ⟨row, found, packed, request, direct, receiver⟩ :=
    newDestination_byteOwner_packed_value config.layout caller.act allocationOrigin knownCount before allocated id created
  have same : row = ready.destination := Option.some.inj (found.symm.trans ready.present)
  subst row
  have allocatedDepth : allocated.activations.length < Goose.Core.maxCallDepth := by
    have acts := congrArg ExecutionState.activations frame.outer
    simpa only [acts] using depth
  have invoked := invokeByteReceiver_body fuel config caller contextId id origin context helper allocated
    contextAt helperAt parameters results ready receiver current allocatedDepth
  have releasedObjects := releaseScope_withoutDeclarations_objects built activation scope pushed.nextScope absent
  let final := { released with activations := released.activations.filter (fun current => current.act != activation.act) }
  refine ⟨final, ?_, finalWorld, ?_, ?_, ?_, ?_, ?_⟩
  · rw [body] at invoked
    exact invoked.trans finish
  · have original := congrArg ExecutionState.objects frame.outer
    have same := congrArg ExecutionState.objects outer
    exact releasedObjects.1.trans (same.trans original)
  · have original := congrArg ExecutionState.objectOrdinals frame.outer
    have same := congrArg ExecutionState.objectOrdinals outer
    exact releasedObjects.2.trans (same.trans original)
  · have original := congrArg ExecutionState.nextAct frame.outer
    have same := congrArg ExecutionState.nextAct outer
    simpa only [final, released, releaseScopeState, scopeState, ownershipResultScopeState, pushed, original] using same
  · have original := congrArg ExecutionState.nextScope frame.outer
    have same := congrArg ExecutionState.nextScope outer
    simpa only [final, released, releaseScopeState, scopeState, ownershipResultScopeState, pushed, original] using same
  · exact ⟨BuiltByteReceiver.of_construction_eq (before := built) (after := final) rfl geometry⟩

#print axioms fresh_byte_call_invoke_world
end Goose.Proofs.ConstructionAcceptedExecution
