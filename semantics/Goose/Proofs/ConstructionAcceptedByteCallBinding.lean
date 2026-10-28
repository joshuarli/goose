import Goose.Proofs.ConstructionAcceptedByteCallConstruct
import Goose.Proofs.ConstructionAcceptedLocalFreshness
import Goose.Proofs.ConstructionAcceptedRegionLimits
import Goose.Proofs.ConstructionAcceptedLocalAdvance

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ExitExecution

private theorem evalM_bind_stop {α β : Type} (action : EvalM α) (next : α → EvalM β)
    (before after : ExecutionState) (reason : Goose.Core.Stop) (step : action before = .stop reason after) :
    (action >>= next) before = .stop reason after := by simp only [bind, step]

private theorem evalM_bind_ok {α β : Type} (action : EvalM α) (next : α → EvalM β)
    (before after : ExecutionState) (value : α) (step : action before = .ok value after) :
    (action >>= next) before = next value after := by simp only [bind, step]

theorem fresh_byteCall_bind_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (caller : RuntimeActivation) (contextId scope localId : Nat) (root : RootInst)
    (bytes : List UInt8) (allocationOrigin origin : OriginId) (context : Context) (helper : Impl) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id : Nat) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (world : AcceptedWorld config frame.initialized before ambient types live [] [])
    (source : AcceptedFrame config accepted frame before types)
    (descriptor : LocalVar) (rootOrder : localId = frame.rootCursor.nextVar) (typingOrder : localId = frame.typingCounter)
    (declared : frame.typing.variables[localId]? = some descriptor) (descriptorType : descriptor.ty = .varr (.int .u8))
    (resolved : rootOf frame.interpretation.environment localId before = .ok root before)
    (conforms : LayoutConforms config.layout (.varr (.int .u8)))
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
      let stored ← (do
        buildExpr (fuel + 1) config caller id (.call contextId [] origin)
        let destination ← completedReceivingDestination id
        publishCarriers allocationOrigin [.completed destination]
        storedDestination destination)
      bindRoot root (.stored { stored with ty := .varr (.int .u8), object := none })) allocated
    match outcome with
    | .stop _ after => ∃ nextAmbient, AcceptedWorld config frame.initialized after nextAmbient types live [freshReceivingRegion before id] []
    | .ok () after => ∃ stored : StoredValue,
        RootTypesExtend types (registerRootType types root (.varr (.int .u8))) ∧
        AcceptedWorld config frame.initialized after ambient (registerRootType types root (.varr (.int .u8)))
          (fun other => other = root ∨ live other) [] [] ∧
        AcceptedFrame config accepted (advanceLocalFrame frame localId) after (registerRootType types root (.varr (.int .u8))) ∧
        stored.storage = before.construction.storage.size ∧ stored.destination = some id
    | _ => False := by
  have uninitialized : frame.rootCursor.nextVar ≤ localId ∨ localId ∈ frame.source.initializing := Or.inl (by rw [rootOrder]; exact Nat.le_refl _)
  have constructed := fresh_byteCall_construct_observed fuel config accepted frame caller contextId scope bytes allocationOrigin origin
    context helper knownCount before allocated id ambient types live world source contextAt helperAt parameters results body absent
    history noRetained noTickets fits depth created
  cases step : (do
      buildExpr (fuel + 1) config caller id (.call contextId [] origin)
      let destination ← completedReceivingDestination id
      publishCarriers allocationOrigin [.completed destination]
      storedDestination destination) allocated with
  | escape target carriers after | jump target kind after => simp [step] at constructed
  | stop reason after =>
    simp only [step] at constructed
    have combined := evalM_bind_stop _ (fun stored => bindRoot root (.stored { stored with ty := .varr (.int .u8), object := none })) allocated after reason step
    rw [combined]
    exact constructed
  | ok stored published =>
    simp only [step] at constructed
    obtain ⟨publishedWorld, publishedSource, backed, storageEq, destinationEq, typeEq, objectNone⟩ := constructed
    have resolvedAfter := rootOf_transfer frame.interpretation localId before published root resolved
    obtain ⟨fresh, freshType, freshSynthetic⟩ := publishedSource.uninitializedLocal_fresh localId root uninitialized resolvedAfter
    have compatible : RootTypeCompatible types root (.varr (.int .u8)) := by
      intro previous present
      rw [publishedSource.uninitializedTypes localId uninitialized root resolvedAfter] at present
      cases present
    have sameStored : { stored with ty := .varr (.int .u8), object := none } = stored := by
      rw [← typeEq]
      cases stored
      simp_all
    have representation : ValueRepresentation (.varr (.int .u8)) (.stored stored) := .stored _ stored rfl typeEq
    obtain ⟨after, bound, extended, finalWorld⟩ := bindRoot_freshStored_extendedWorld config frame.initialized published ambient types live root
      (.varr (.int .u8)) stored [] [] publishedWorld compatible conforms representation backed fresh
      (by intro region member; cases member) (by intro region member; cases member) freshType freshSynthetic
    have advanced := publishedSource.bindFreshStored_advance publishedWorld localId descriptor root stored rootOrder typingOrder
      declared (typeEq.trans descriptorType.symm) (by rw [descriptorType]; rfl) resolvedAfter bound
    have combined := evalM_bind_ok _ (fun stored => bindRoot root (.stored { stored with ty := .varr (.int .u8), object := none })) allocated published stored step
    rw [combined, sameStored, bound]
    exact ⟨stored, extended, finalWorld, by simpa only [descriptorType] using advanced, storageEq, destinationEq⟩

#print axioms fresh_byteCall_bind_world
end Goose.Proofs.ConstructionAcceptedExecution
