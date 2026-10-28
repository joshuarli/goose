import Goose.Proofs.ConstructionExitDirectFreshWorld
import Goose.Proofs.ConstructionAcceptedByteReturnProduce
import Goose.Proofs.ConstructionExitEvaluationHistoryCompletion
import Goose.Proofs.ConstructionExitByteBacking
import Goose.Proofs.ConstructionAcceptedByteNormalized

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem completion_byteReceiver_normalized_observed_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion)
    (world : AcceptedWorld config initialized before ambient types live regions [])
    (history : ReservationReferencesBounded before.construction ambient)
    (noRetained : completedCarrierIds ambient.retained = [])
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed) (adaptation : ready.destination.adaptation = none)
    (receiver : ready.destination.use = .receiver) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id) (fits : bytes.length < 2 ^ 32)
    (mutable : ∀ region ∈ regions, id ∈ region.mutableDestinations)
    (cutoff : ∀ region ∈ regions, region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (covered : ∀ root, live root → ∃ region ∈ regions, ¬ region.mutableRoots root) :
    let token := before.construction.exitReservations.size
    let waited := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.waiting id) } }
    ∃ after,
      evalProduce (fuel + 2) config environment [.completion token] (.bytes (.varr (.int .u8)) bytes origin) waited =
        .ok [.completed id] after ∧
      AcceptedWorld config initialized after (.exitChannels [token] [] [.completed id] :: ambient) types live regions [] ∧
      after.construction.exitReservations[token]? = some (.active .fresh id id ready.destination) ∧
      CarriersLandingReady after [.construct id] [.completed id] ∧
      (∀ carrier ∈ [.completed id], CarrierResultBacking config.layout after carrier) ∧
      after = { before with construction := after.construction } ∧
      (ready.destination.capability.layout = .varr (.int .u8) →
        Nonempty (NormalizedCompletedCarrier after (.varr (.int .u8)) id)) := by
  let token := before.construction.exitReservations.size
  let waited := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push (.waiting id) } }
  let prepared := { before with construction := { before.construction with
    exitReservations := before.construction.exitReservations.push (.active .fresh id id ready.destination) } }
  let preparedReady : OpenDestinationBacking config.layout prepared id (.varr (.int .u8)) 0 :=
    { ready with present := ready.present, bytes := ready.bytes }
  have preparedWorld : AcceptedWorld config initialized prepared (.exitChannels [token] [] [.completed id] :: ambient) types live regions [] :=
    direct_fresh_acceptedWorld config initialized before ambient types live regions id ready.destination [.completed id] world history ready.present ready.opened current noRetained
  have preparedCurrent : destinationCurrent prepared.construction id = .ok id := by
    rw [destinationCurrent_congr_tables before.construction prepared.construction rfl rfl id]
    exact current
  have selection := wait_then_select_completion_open_byte before environment id ready.destination (.varr (.int .u8)) bytes origin
    ready.present ready.opened current
  have selected : selectCompletionChannel environment (.bytes (.varr (.int .u8)) bytes origin) (.completion token) waited =
      .ok (.construct id) prepared := by
    simpa [token, waited, prepared, Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, Array.set_push] using selection.2
  have preparedPresent : prepared.construction.destinations[id]? = some ready.destination := ready.present
  have renewal : renewReceivingDestination id prepared.construction = .ok id prepared.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, preparedCurrent, pure,
      lookupDestination_result, preparedPresent, ready.opened]
  have action : evalProduce (fuel + 2) config environment [.completion token] (.bytes (.varr (.int .u8)) bytes origin) waited =
      evalProduce (fuel + 2) config environment [.construct id] (.bytes (.varr (.int .u8)) bytes origin) prepared := by
    simp only [evalProduce, List.mapM_cons, List.mapM_nil, liftConstruction, renewal, bind, pure,
      selected]
    simp [selectCompletionChannel, pure]
  obtain ⟨after, produced, built, result⟩ := evalProduce_byteReceiver_built_world fuel config initialized environment id bytes origin
    prepared (.exitChannels [token] [] [.completed id] :: ambient) types live regions preparedWorld preparedReady packed adaptation receiver
    request preparedCurrent fits mutable cutoff covered
  have tickets := buildExpr_bytes_tickets fuel config environment id (.varr (.int .u8)) bytes origin prepared after
    ready.destination 0 preparedWorld.ownership.source preparedCurrent ready.present ready.opened built
  have ticket : after.construction.exitReservations[token]? = some (.active .fresh id id ready.destination) := by
    rw [tickets]
    simp [prepared, token]
  obtain ⟨backed, ⟨landing⟩, landed⟩ := accepted_byte_receiver_landing_ready fuel config initialized environment bytes origin id 0
    prepared after (.exitChannels [token] [] [.completed id] :: ambient) types live regions [] preparedWorld preparedReady
    packed request receiver (by simpa using fits) preparedCurrent built
  have targetReady : CarriersLandingReady after [.construct id] [.completed id] := by
    refine ⟨rfl, ?_⟩
    intro channel carrier member
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl⟩ := member
    exact .construct id id landing
  have targetBacked : ∀ carrier ∈ [.completed id], CarrierResultBacking config.layout after carrier := by
    intro carrier member
    simp only [List.mem_singleton] at member
    subst carrier
    exact backed
  have runtime := buildExpr_bytes_runtime fuel config environment id (.varr (.int .u8)) bytes origin prepared after
    ready.destination 0 preparedWorld.ownership.source preparedCurrent ready.present ready.opened built
  have outer : after = { before with construction := after.construction } := by simpa only [prepared] using runtime
  have normalized : ready.destination.capability.layout = .varr (.int .u8) →
      Nonempty (NormalizedCompletedCarrier after (.varr (.int .u8)) id) := by
    intro physical
    exact packed_byte_build_normalized fuel config environment id bytes origin prepared after preparedWorld.ownership.source
      preparedReady packed request receiver adaptation physical preparedCurrent fits built
  exact ⟨after, action.trans produced, result, ticket, targetReady, targetBacked, outer, normalized⟩



theorem completion_byteReceiver_observed_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion)
    (world : AcceptedWorld config initialized before ambient types live regions [])
    (history : ReservationReferencesBounded before.construction ambient)
    (noRetained : completedCarrierIds ambient.retained = [])
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed) (adaptation : ready.destination.adaptation = none)
    (receiver : ready.destination.use = .receiver) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id) (fits : bytes.length < 2 ^ 32)
    (mutable : ∀ region ∈ regions, id ∈ region.mutableDestinations)
    (cutoff : ∀ region ∈ regions, region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (covered : ∀ root, live root → ∃ region ∈ regions, ¬ region.mutableRoots root) :
    let token := before.construction.exitReservations.size
    let waited := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.waiting id) } }
    ∃ after,
      evalProduce (fuel + 2) config environment [.completion token] (.bytes (.varr (.int .u8)) bytes origin) waited =
        .ok [.completed id] after ∧
      AcceptedWorld config initialized after (.exitChannels [token] [] [.completed id] :: ambient) types live regions [] ∧
      after.construction.exitReservations[token]? = some (.active .fresh id id ready.destination) ∧
      CarriersLandingReady after [.construct id] [.completed id] ∧
      (∀ carrier ∈ [.completed id], CarrierResultBacking config.layout after carrier) ∧
      after = { before with construction := after.construction } := by
  obtain ⟨after, produced, afterWorld, ticket, targetReady, targetBacked, outer, normalized⟩ :=
    completion_byteReceiver_normalized_observed_world fuel config initialized environment id bytes origin before ambient types live regions
      world history noRetained ready packed adaptation receiver request current fits mutable cutoff covered
  exact ⟨after, produced, afterWorld, ticket, targetReady, targetBacked, outer⟩

theorem completion_byteReceiver_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion)
    (world : AcceptedWorld config initialized before ambient types live regions [])
    (history : ReservationReferencesBounded before.construction ambient)
    (noRetained : completedCarrierIds ambient.retained = [])
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed) (adaptation : ready.destination.adaptation = none)
    (receiver : ready.destination.use = .receiver) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id) (fits : bytes.length < 2 ^ 32)
    (mutable : ∀ region ∈ regions, id ∈ region.mutableDestinations)
    (cutoff : ∀ region ∈ regions, region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (covered : ∀ root, live root → ∃ region ∈ regions, ¬ region.mutableRoots root) :
    let token := before.construction.exitReservations.size
    let waited := { before with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push (.waiting id) } }
    ∃ after,
      evalProduce (fuel + 2) config environment [.completion token] (.bytes (.varr (.int .u8)) bytes origin) waited =
        .ok [.completed id] after ∧
      AcceptedWorld config initialized after (.exitChannels [token] [] [.completed id] :: ambient) types live regions [] ∧
      after.construction.exitReservations[token]? = some (.active .fresh id id ready.destination) ∧
      CarriersLandingReady after [.construct id] [.completed id] ∧
      (∀ carrier ∈ [.completed id], CarrierResultBacking config.layout after carrier) := by
  obtain ⟨after, produced, afterWorld, ticket, targetReady, targetBacked, outer⟩ :=
    completion_byteReceiver_observed_world fuel config initialized environment id bytes origin before ambient types live regions
      world history noRetained ready packed adaptation receiver request current fits mutable cutoff covered
  exact ⟨after, produced, afterWorld, ticket, targetReady, targetBacked⟩

#print axioms completion_byteReceiver_world
#print axioms completion_byteReceiver_observed_world
#print axioms completion_byteReceiver_normalized_observed_world
end Goose.Proofs.ConstructionAcceptedExecution
