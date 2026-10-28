import Goose.Proofs.ConstructionExitSampledBind

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

def builtDestinationStored (id count : Nat) (row : PendingDestination) : StoredValue :=
  ⟨row.storage, row.capability.start, row.capability.logicalType, count, some id, none, [], count⟩

theorem bind_built_destination_accepted_world (config : EvalConfig) (initialized : Nat)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (root : RootInst) (ty : Ty)
    (id count : Nat) (row : PendingDestination) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
    (rooted : rootOf environment localVar state = .ok root state)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (carrier : CarrierResultBacking config.layout state (.completed id))
    (present : state.construction.destinations[id]? = some row) (built : row.progress = .built count)
    (compatible : RootTypeCompatible types root ty) (conforms : LayoutConforms config.layout ty)
    (represented : ValueRepresentation ty (.stored (builtDestinationStored id count row)))
    (fresh : state.objectOrdinals.lookup root = none)
    (regionSafety : ∀ region ∈ regions, ¬ region.mutableRoots root →
      StoredBackingObservation config.layout state region.limit (builtDestinationStored id count row) ∧
        ∀ other, (builtDestinationStored id count row).destination = some other → other ∉ region.mutableDestinations)
    (freshType : ∀ act scope index, root = .local act scope index → act < state.nextAct ∧ scope < state.nextScope)
    (freshSynthetic : ∀ index, root = .global index → config.module.globals.size ≤ index →
      index < config.module.globals.size + state.nextScope) :
    ∃ after, storedDestination id state = .ok (builtDestinationStored id count row) state ∧
      bindRoot root (.stored (builtDestinationStored id count row)) state = .ok () after ∧
      (do let location ← rootOf environment localVar; let value ← carrierValue (.completed id); bindRoot location value) state = .ok () after ∧
      after.objects.lookup root = some (.stored (builtDestinationStored id count row)) ∧
      storedDestination id after = .ok (builtDestinationStored id count row) after ∧
      RootTypesExtend types (registerRootType types root ty) ∧
      AcceptedWorld config initialized after ambient (registerRootType types root ty)
        (fun other => other = root ∨ live other) regions pending := by
  obtain ⟨sample, boundState, sampled, bound, value, alias, sampledCount, construction, resampled⟩ :=
    bind_built_destination_alias state root id count row present built
  have canonical : sample = builtDestinationStored id count row := by
    have result : storedDestination id state = .ok (builtDestinationStored id count row) state := by
      simp [storedDestination, getDestination, EvalM.get, present, bind, built, progressCount, pure, builtDestinationStored]
    exact (ExecutionStep.ok.inj (sampled.symm.trans result)).1
  subst sample
  have backing : StoredValueBacking config.layout state (builtDestinationStored id count row) := by
    cases carrier with
    | completed carrierId carrierCount destination stored found phase sampledCarrier backed =>
      have same : stored = builtDestinationStored id count row := (ExecutionStep.ok.inj (sampledCarrier.symm.trans sampled)).1
      simpa only [same] using backed
  obtain ⟨after, actual, extended, accepted⟩ := bindRoot_freshStored_world config initialized state ambient types live root ty
    (builtDestinationStored id count row) world compatible conforms represented backing fresh regionSafety freshType freshSynthetic
  have same : boundState = after := (ExecutionStep.ok.inj (bound.symm.trans actual)).2
  subst after
  refine ⟨boundState, sampled, bound, ?_, value, resampled, extended, accepted⟩
  simp only [bind, rooted, carrierValue, sampled, pure, bound]

#print axioms bind_built_destination_accepted_world

end Goose.Proofs.ConstructionAcceptedExecution
