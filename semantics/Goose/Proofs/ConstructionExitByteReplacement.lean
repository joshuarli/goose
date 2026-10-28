import Goose.Proofs.ConstructionExitByteBacking
import Goose.Proofs.ConstructionAcceptedFreshness

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem accepted_byte_replacement_produce_unwind (fuel : Nat) (config : EvalConfig)
    (initialized : Nat) (environment : RuntimeActivation) (bytes : List UInt8)
    (origin : Goose.Core.OriginId) (id parent count : Nat) (before after : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (openBacking : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : openBacking.destination.layout = .packed)
    (request : openBacking.destination.capability.request = .value)
    (replacement : openBacking.destination.use = .replacement parent)
    (fits : count + bytes.length < 2 ^ 32)
    (current : destinationCurrent before.construction id = .ok id)
    (built : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after)
    (scope : Nat) (scopeInst : Goose.Core.ScopeInst) :
    let unwound := releaseScopeState environment scope scopeInst after
    evalProduce (fuel + 2) config environment [.construct id] (.bytes (.varr (.int .u8)) bytes origin) before =
      .ok [.completed id] after ∧
    OwnershipSourceState unwound.construction ∧
    CarrierResultBacking config.layout unwound (.completed id) ∧
    ∃ destination, unwound.construction.destinations[id]? = some destination ∧
      destination.use = .replacement parent ∧ destination.progress = .built (count + bytes.length) ∧
      ∃ owner, unwound.construction.destinations[parent]? = some owner ∧
        destination.backing = owner.backing ∧
        ((∃ n, owner.progress = .exiting n id) ∨ owner.progress = .abandoned ∨ owner.progress = .cancelled) := by
  have backed := accepted_byte_return_carrier_backed fuel config initialized environment bytes origin id count
    before after ambient types live regions pending world openBacking packed request fits current built
  obtain ⟨destination, storage, present, _, _, _, _, _, use, progress, _⟩ :=
    buildExpr_byteOwner_geometry fuel config environment bytes origin id count before after
      openBacking packed request fits world.ownership.source.structural.1.1.1 current built
  have source := buildExpr_bytes_sourceState fuel config environment id (.varr (.int .u8)) bytes origin
    before after openBacking.destination count world.ownership.source current openBacking.present openBacking.opened built
  have terminal := destinationSuccessorKeysInactive_built_terminal after.construction source.inactiveKeys id
    destination present (count + bytes.length) progress
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have resolved : destinationCurrent after.construction id = .ok id := by
    simp only [destinationCurrent_result, destinationCurrentSteps_succ, inside, ↓reduceIte, terminal]
  have complete : completedReceivingDestination id after = .ok id after := by
    simp only [completedReceivingDestination, receivingDestination, liftConstruction, resolved,
      bind, completedDestination, getDestination, EvalM.get, present, progress, pure]
  have renewal : renewReceivingDestination id before.construction = .ok id before.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, openBacking.present, openBacking.opened]
  have supported : ReplacementSupported after.construction id :=
    .active id destination present (by simp only [progress, activeProgress])
  have owner := source.structural.1.2.2.1 id parent destination present (use.trans replacement) supported
  refine ⟨?_, source, carrierBacking_construction_frame config.layout after
    (releaseScopeState environment scope scopeInst after) rfl _ backed,
    destination, present, use.trans replacement, progress, owner⟩
  simp only [evalProduce, List.mapM_cons, List.mapM_nil, liftConstruction, renewal, bind, pure,
    selectCompletionChannel, built, complete]

#print axioms accepted_byte_replacement_produce_unwind

end Goose.Proofs.ConstructionAcceptedExecution
