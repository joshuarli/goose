import Goose.Proofs.ConstructionExitDirectByteLoop
import Goose.Proofs.ConstructionExitByteRegions
import Goose.Proofs.ConstructionAcceptedBytePublication

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem evalProduce_byteReceiver_built_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion)
    (world : AcceptedWorld config initialized before ambient types live regions [])
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed)
    (adaptation : ready.destination.adaptation = none)
    (receiver : ready.destination.use = .receiver)
    (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id)
    (fits : bytes.length < 2 ^ 32)
    (mutable : ∀ region ∈ regions, id ∈ region.mutableDestinations)
    (cutoff : ∀ region ∈ regions, region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (covered : ∀ root, live root → ∃ region ∈ regions, ¬ region.mutableRoots root) :
    ∃ after,
      evalProduce (fuel + 2) config environment [.construct id] (.bytes (.varr (.int .u8)) bytes origin) before =
        .ok [.completed id] after ∧
      buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after ∧
      AcceptedWorld config initialized after ambient types live regions [] := by
  obtain ⟨after, built⟩ := packed_receiver_byte_build fuel config environment bytes origin before id 0
    ready.destination ready.storage ready.present ready.bytes ready.opened packed adaptation receiver request current (by simpa using fits)
  have afterSource := buildExpr_bytes_sourceState fuel config environment id (.varr (.int .u8)) bytes origin before after
    ready.destination 0 world.ownership.source current ready.present ready.opened built
  obtain ⟨destination, storage, found, _, _, _, _, _, use, progress, _⟩ :=
    buildExpr_byteOwner_geometry fuel config environment bytes origin id 0 before after ready packed request
      (by simpa using fits) world.ownership.source.structural.1.1.1 current built
  have terminal := destinationSuccessorKeysInactive_built_terminal after.construction afterSource.inactiveKeys id destination found
    (0 + bytes.length) progress
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have currentAfter : destinationCurrent after.construction id = .ok id := by
    simp only [destinationCurrent_result, destinationCurrentSteps_succ, inside, ↓reduceIte, terminal]
  have renewal : renewReceivingDestination id before.construction = .ok id before.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, ready.present, ready.opened]
  have completed : completedReceivingDestination id after = .ok id after := by
    simp only [completedReceivingDestination, receivingDestination, liftConstruction, currentAfter,
      bind, completedDestination, getDestination, EvalM.get, found, progress, pure]
  refine ⟨after, ?_, built, ?_⟩
  · simp only [evalProduce, List.mapM_cons, List.mapM_nil, liftConstruction, renewal, bind, pure,
      selectCompletionChannel, built, completed]
  · exact packed_byte_build_accepted_world fuel config initialized environment id 0 bytes origin before after ambient types live regions
      world ready packed request (by simpa using fits) current mutable cutoff covered built



#print axioms evalProduce_byteReceiver_built_world
end Goose.Proofs.ConstructionAcceptedExecution
