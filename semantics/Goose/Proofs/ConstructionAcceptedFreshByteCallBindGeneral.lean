import Goose.Proofs.ConstructionAcceptedFreshByteCallConstructGeneral
import Goose.Proofs.ConstructionAcceptedByteCallBinding

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution
open Goose.Proofs.ConstructionRootCorrespondence

private theorem evalM_bind_stop {α β : Type} (action : EvalM α) (next : α → EvalM β)
    (before after : ExecutionState) (reason : Goose.Core.Stop) (step : action before = .stop reason after) :
    (action >>= next) before = .stop reason after := by simp only [bind, step]

private theorem evalM_bind_ok {α β : Type} (action : EvalM α) (next : α → EvalM β)
    (before after : ExecutionState) (value : α) (step : action before = .ok value after) :
    (action >>= next) before = next value after := by simp only [bind, step]

theorem fresh_byteCall_bind_pending (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (caller : RuntimeActivation) (contextId scope localId : Nat) (root : RootInst)
    (bytes : List UInt8) (allocationOrigin origin : OriginId) (context : Context) (helper : Impl) (knownCount : Option Nat)
    (before allocated : ExecutionState) (id : Nat) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (coverage : EvaluationHistoryCoverage before ambient pending)
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
    | .stop _ after => ∃ nextAmbient, AcceptedWorld config frame.initialized after nextAmbient types live (freshReceivingRegion before id :: regions) pending
    | .ok () after => ∃ stored : StoredValue,
        RootTypesExtend types (registerRootType types root (.varr (.int .u8))) ∧
        AcceptedWorld config frame.initialized after ambient (registerRootType types root (.varr (.int .u8)))
          (fun other => other = root ∨ live other)
          (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent after stored.storage))) pending ∧
        AcceptedFrame config accepted (advanceLocalFrame frame localId) after (registerRootType types root (.varr (.int .u8))) ∧
        stored.storage = before.construction.storage.size ∧ stored.destination = some id
    | _ => False := by
  have uninitialized : frame.rootCursor.nextVar ≤ localId ∨ localId ∈ frame.source.initializing := Or.inl (by rw [rootOrder]; exact Nat.le_refl _)
  have constructed := fresh_byteCall_construct_pending fuel config accepted frame caller contextId scope bytes allocationOrigin origin
    context helper knownCount before allocated id ambient types live regions pending world coverage source contextAt helperAt parameters results body absent
    fits depth created
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
    obtain ⟨publishedWorld, publishedSource, backed, storageEq, destinationEq, typeEq, objectNone, ordinals, acts, scopes, ⟨publishedFrame⟩⟩ := constructed
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
    obtain ⟨freshBefore, freshTypeBefore, freshSyntheticBefore⟩ := source.uninitializedLocal_fresh localId root uninitialized resolved
    have freshId := newDestination_fresh_id config.layout caller.act (.varr (.int .u8)) .value allocationOrigin knownCount before allocated id created
    obtain ⟨after, bound, extended, finalWorld⟩ := freshByteCall_bind_world config frame.initialized before published publishedFrame
      ordinals acts scopes stored root (.varr (.int .u8)) ambient types live regions pending world publishedWorld representation backed
      storageEq (by simpa only [freshId] using destinationEq) compatible conforms freshBefore freshTypeBefore freshSyntheticBefore
    have advanced := publishedSource.bindFreshStored_advance publishedWorld localId descriptor root stored rootOrder typingOrder
      declared (typeEq.trans descriptorType.symm) (by rw [descriptorType]; rfl) resolvedAfter bound
    have combined := evalM_bind_ok _ (fun stored => bindRoot root (.stored { stored with ty := .varr (.int .u8), object := none })) allocated published stored step
    rw [combined, sameStored, bound]
    have sameConstruction : after.construction = published.construction := by
      cases ordinal : published.objectOrdinals.lookup root <;>
        simp only [bindRoot, bind, EvalM.get, ordinal, Option.isNone, Bool.false_eq_true, ite_false,
          ite_true, setObjectOrdinal, EvalM.set, bindStaticRoot] at bound <;>
        cases bound <;> rfl
    exact ⟨stored, extended, by simpa only [storageExtent, sameConstruction] using finalWorld, by simpa only [descriptorType] using advanced, storageEq, destinationEq⟩

#print axioms fresh_byteCall_bind_pending
end Goose.Proofs.ConstructionAcceptedExecution
