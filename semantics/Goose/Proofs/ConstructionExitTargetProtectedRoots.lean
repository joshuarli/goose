import Goose.Proofs.ConstructionExitTargetByteReadiness
import Goose.Proofs.ConstructionExitByteProtectedBuild
import Goose.Proofs.ConstructionExitDirectRead

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem checked_byte_returnFrom_protected_roots (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (source target : RuntimeActivation) (targetId id : Nat) (bytes : List UInt8) (origin : OriginId)
    (initial : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (region : ReceivingRegion)
    (world : AcceptedWorld config initialized initial ambient types live regions pending)
    (history : EvaluationHistoryCoverage initial ambient pending)
    (ready : OpenDestinationBacking config.layout initial id (.varr (.int .u8)) 0)
    (selection : targetActivation config targetId initial = .ok target initial)
    (channels : target.channels = [.construct id]) (regionMember : region ∈ regions) (regionDestination : region.destination = id)
    (receiver : ready.destination.use = .receiver) (packed : ready.destination.layout = .packed)
    (adaptation : ready.destination.adaptation = none) (physical : ready.destination.capability.layout = .varr (.int .u8))
    (request : ready.destination.capability.request = .value)
    (current : destinationCurrent initial.construction id = .ok id) (fits : bytes.length < 2 ^ 32) :
    ∃ after : ExecutionState,
      let token := initial.construction.exitReservations.size
      let cleaned := { after with construction := { after.construction with
        exitReservations := after.construction.exitReservations.set! token .released } }
      execStmt (fuel + 4) config source (.returnFrom targetId [.bytes (.varr (.int .u8)) bytes origin] origin) initial =
        .escape ⟨target.act, .nonlocal targetId⟩ [.completed id] cleaned ∧
      LandedResultChannels cleaned target.channels [.varr (.int .u8)] [.completed id] ∧
      RootedBackingObservations config.layout cleaned (fun root => live root ∧ ¬ region.mutableRoots root) region.limit ∧
      (validate config.module = .ok () → ∀ location, (live location.root ∧ ¬ region.mutableRoots location.root) → ∀ readFuel,
        mapStepState (fun _ => ExecutionState.initial) (readLoc readFuel config.layout location cleaned) =
        mapStepState (fun _ => ExecutionState.initial) (readLoc readFuel config.layout location initial)) ∧
      EvaluationHistoryLifecycle cleaned (.returned [.completed id] :: ambient) (⟨target.channels, [.completed id]⟩ :: pending) := by
  have protection := world.protections region regionMember
  have rootReceiver : region.destination ∈ region.mutableDestinations := protection.authority
  have mutable : id ∈ region.mutableDestinations := by simpa only [regionDestination] using rootReceiver
  have present : initial.construction.destinations[region.destination]? = some ready.destination := by
    simpa only [regionDestination] using ready.present
  have cutoff : region.limit ready.destination.storage ≤ ready.destination.capability.start := protection.landing ready.destination present
  obtain ⟨after, escaped, _, _, landed, prefixes, objects, ordinals, rows⟩ :=
    direct_byte_return_cleanup fuel config source target targetId id bytes origin initial ready world.ownership.source selection channels
      receiver packed adaptation physical request current fits
  let token := initial.construction.exitReservations.size
  let cleaned := { after with construction := { after.construction with
    exitReservations := after.construction.exitReservations.set! token .released } }
  have cleanPrefixes : StoragePrefixesEqual region.limit initial.construction.storage cleaned.construction.storage :=
    prefixes region.limit cutoff
  have cleanObjects : cleaned.objects = initial.objects := objects
  have cleanOrdinals : cleaned.objectOrdinals = initial.objectOrdinals := ordinals
  have cleanRows : ∀ root, (live root ∧ ¬ region.mutableRoots root) → ∀ value,
      initial.objects.lookup root = some value → ∀ stored, StoredOccurrence value stored → ∀ selected,
      stored.destination = some selected → cleaned.construction.destinations[selected]? = initial.construction.destinations[selected]? := by
    intro root retained value found stored occurrence selected named
    have excluded := protection.names root retained.1 retained.2 value found stored occurrence selected named
    have different : selected ≠ id := by
      intro equal
      subst selected
      exact excluded mutable
    exact rows selected different
  have observations := rootedBackingObservations_storagePrefixes config.layout initial cleaned _ region.limit
    protection.observations cleanPrefixes cleanObjects cleanOrdinals cleanRows
  have tracked := evaluator_history_outcome (fuel + 4) config .none _
    (.statement source (.returnFrom targetId [.bytes (.varr (.int .u8)) bytes origin] origin)) initial ambient pending target.channels
    ⟨world.ownership.source.structural.1.1, history⟩
  have afterHistory : EvaluationHistoryLifecycle cleaned (.returned [.completed id] :: ambient)
      (⟨target.channels, [.completed id]⟩ :: pending) := by
    simpa only [escaped, EvaluationHistoryLifecycleOutcome] using tracked
  refine ⟨after, escaped, ?_, observations, ?_, afterHistory⟩
  · simpa only [channels] using landed
  · intro accepted location retained readFuel
    apply direct_exit_outside_read readFuel config accepted initial cleaned _ region.limit id
      protection.observations cleanPrefixes (by intros; rw [cleanObjects]) (by intros; rw [cleanOrdinals])
    · intro other different
      exact rows other different
    · intro root kept value found stored occurrence named
      exact protection.names root kept.1 kept.2 value found stored occurrence id named mutable
    · exact retained

#print axioms checked_byte_returnFrom_protected_roots

end Goose.Proofs.ConstructionAcceptedExecution
