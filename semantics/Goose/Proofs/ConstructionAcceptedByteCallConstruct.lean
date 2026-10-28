import Goose.Proofs.ConstructionAcceptedByteCallBuild
import Goose.Proofs.ConstructionAcceptedByteInvokePublish

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem fresh_byteCall_construct_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
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
      buildExpr (fuel + 1) config caller id (.call contextId [] origin)
      let destination ← completedReceivingDestination id
      publishCarriers allocationOrigin [.completed destination]
      storedDestination destination) allocated
    match outcome with
    | .stop _ after => ∃ nextAmbient, AcceptedWorld config frame.initialized after nextAmbient types live [freshReceivingRegion before id] []
    | .ok stored after =>
        AcceptedWorld config frame.initialized after ambient types live [] [] ∧
        AcceptedFrame config accepted frame after types ∧ StoredValueBacking config.layout after stored ∧
        stored.storage = before.construction.storage.size ∧ stored.destination = some id ∧ stored.ty = .varr (.int .u8)
    | _ => False := by
  have published := fresh_byteInvoke_publish_world fuel config accepted frame caller contextId scope bytes allocationOrigin origin context helper
    knownCount before allocated id ambient types live world source contextAt helperAt parameters results body absent history noRetained noTickets fits depth created
  have built := fresh_byteCall_build fuel config frame.initialized caller contextId scope bytes allocationOrigin origin context helper
    knownCount before allocated id ambient types live world contextAt helperAt parameters results body absent history noRetained noTickets fits depth created
  cases invoked : invokeCall fuel config caller contextId [] [.construct id] origin allocated with
  | escape target carriers after | jump target kind after => simp [invoked] at built
  | stop reason after =>
    simp only [invoked] at published built
    simp only [built, bind]
    simpa only [invoked, bind] using published
  | ok carriers returned =>
    simp only [invoked] at built
    obtain ⟨same, builtEq, completed⟩ := built
    subst carriers
    cases publication : publishCarriers allocationOrigin [.completed id] returned with
    | escape target carriers after | jump target kind after =>
      simp [invoked, bind, publication] at published
    | stop reason after =>
      simp [invoked, bind, publication] at published
      obtain ⟨nextAmbient, finalWorld⟩ := published
      simp only [builtEq, completed, publication, bind]
      exact ⟨nextAmbient, finalWorld⟩
    | ok value after =>
      cases value
      simp only [invoked, bind, publication, pure] at published
      obtain ⟨stored, same, finalWorld, finalFrame, sampled, backed, storageEq, destinationEq, typeEq⟩ := published
      simp only [builtEq, completed, publication, sampled, bind]
      exact ⟨finalWorld, finalFrame, backed, storageEq, destinationEq, typeEq⟩

#print axioms fresh_byteCall_construct_world
end Goose.Proofs.ConstructionAcceptedExecution
