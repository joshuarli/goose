import Goose.Proofs.ConstructionExitByteBacking
import Goose.Proofs.ConstructionAcceptedFreshness

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem accepted_byte_construct_produce_unwind (fuel : Nat) (config : EvalConfig)
    (initialized : Nat) (environment : RuntimeActivation) (bytes : List UInt8)
    (origin : Goose.Core.OriginId) (id count : Nat) (before after : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (openBacking : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : openBacking.destination.layout = .packed)
    (request : openBacking.destination.capability.request = .value)
    (receiver : openBacking.destination.use = .receiver)
    (fits : count + bytes.length < 2 ^ 32)
    (current : destinationCurrent before.construction id = .ok id)
    (built : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after)
    (scope : Nat) (scopeInst : Goose.Core.ScopeInst) :
    evalProduce (fuel + 2) config environment [.construct id] (.bytes (.varr (.int .u8)) bytes origin) before =
      .ok [.completed id] after ∧
    CarrierResultBacking config.layout (releaseScopeState environment scope scopeInst after) (.completed id) ∧
    CarrierLandingReady (releaseScopeState environment scope scopeInst after) (.construct id) (.completed id) ∧
    landCarriersInto origin [.construct id] [.completed id] (releaseScopeState environment scope scopeInst after) =
      .ok () (releaseScopeState environment scope scopeInst after) := by
  obtain ⟨backed, ⟨ready⟩, landed⟩ := accepted_byte_receiver_landing_ready fuel config initialized environment bytes origin id count
    before after ambient types live regions pending world openBacking packed request receiver fits current built
  have renewal : renewReceivingDestination id before.construction = .ok id before.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, openBacking.present, openBacking.opened]
  have resolved : destinationCurrent after.construction id = .ok id := by
    cases backed with
    | completed _ n destination stored present progress sampled backing =>
      have source := buildExpr_bytes_sourceState fuel config environment id (.varr (.int .u8)) bytes origin
        before after openBacking.destination count world.ownership.source current openBacking.present openBacking.opened built
      have terminal := destinationSuccessorKeysInactive_built_terminal after.construction source.inactiveKeys id destination present n progress
      have inside := (Array.getElem?_eq_some_iff.mp present).1
      simp only [destinationCurrent_result, destinationCurrentSteps_succ, inside, ↓reduceIte, terminal]
  have complete : completedReceivingDestination id after = .ok id after := by
    cases backed with
    | completed _ n destination stored present progress sampled backing =>
      simp only [completedReceivingDestination, receivingDestination, liftConstruction, resolved,
        bind, completedDestination, getDestination, EvalM.get, present, progress, pure]
  refine ⟨?_, carrierBacking_construction_frame config.layout after (releaseScopeState environment scope scopeInst after) rfl _ backed,
    carrierReady_construction_frame after (releaseScopeState environment scope scopeInst after) rfl _ _ (.construct id id ready), ?_⟩
  · simp only [evalProduce, List.mapM_cons, List.mapM_nil, liftConstruction, renewal, bind, pure,
      selectCompletionChannel, built, complete]
  · simp only [releaseScopeState, landCarriersInto, List.length_cons, List.length_nil, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons,
      List.forIn_nil, receivingDestination, liftConstruction, resolved, bind, pure]

#print axioms accepted_byte_construct_produce_unwind

end Goose.Proofs.ConstructionAcceptedExecution
