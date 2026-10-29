import Goose.Proofs.ConstructionAcceptedFreshByteAllFuelGeneral
import Goose.Proofs.ConstructionAcceptedByteCallBuild

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem fresh_byteCall_build_pending (fuel : Nat) (config : EvalConfig) (initialized : Nat)
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
    | .stop reason after => buildExpr (fuel + 1) config caller id (.call contextId [] origin) allocated = .stop reason after
    | .ok carriers after => carriers = [.completed id] ∧
        buildExpr (fuel + 1) config caller id (.call contextId [] origin) allocated = .ok () after ∧
        completedReceivingDestination id after = .ok id after
    | _ => False := by
  have observed := fresh_byteInvoke_pending_allFuel fuel config initialized caller contextId scope bytes allocationOrigin origin context helper
    knownCount before allocated id ambient types live regions pending world coverage contextAt helperAt parameters results body absent fits depth created
  obtain ⟨ready⟩ := newDestination_initial_backing config.layout caller.act (.varr (.int .u8)) .value allocationOrigin
    knownCount before allocated id (.int .u8) rfl created
  have current := newDestination_current_self config initialized caller.act (.varr (.int .u8)) .value allocationOrigin
    knownCount before allocated id ambient types live regions pending world created
  have renewal : renewReceivingDestination id allocated.construction = .ok id allocated.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, ready.present, ready.opened]
  cases invoked : invokeCall fuel config caller contextId [] [.construct id] origin allocated with
  | escape target carriers after | jump target kind after => simp [invoked] at observed
  | stop reason after =>
    simp only [invoked] at observed ⊢
    simp [buildExpr, liftConstruction, renewal, bind, protectDestination, invoked]
  | ok carriers after =>
    simp only [invoked] at observed ⊢
    obtain ⟨same, afterWorld, objects, ordinals, acts, scopes, ⟨facts⟩⟩ := observed
    subst carriers
    have terminal := destinationSuccessorKeysInactive_built_terminal after.construction afterWorld.ownership.source.inactiveKeys
      id facts.row facts.present bytes.length facts.progress
    have inside := (Array.getElem?_eq_some_iff.mp facts.present).1
    have currentAfter : destinationCurrent after.construction id = .ok id := by
      simp only [destinationCurrent_result, destinationCurrentSteps_succ, inside, ↓reduceIte, terminal]
    have complete : completedReceivingDestination id after = .ok id after := by
      simp [completedReceivingDestination, receivingDestination, liftConstruction, currentAfter,
        completedDestination, getDestination, EvalM.get, facts.present, facts.progress, bind, pure]
    refine ⟨rfl, ?_, complete⟩
    simp [buildExpr, liftConstruction, renewal, bind, protectDestination, invoked,
      singleCarrier, receivingDestination, currentAfter, getDestination, EvalM.get, facts.present, pure]

#print axioms fresh_byteCall_build_pending
end Goose.Proofs.ConstructionAcceptedExecution
