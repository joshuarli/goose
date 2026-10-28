import Goose.Proofs.ConstructionExitNamedPublishedActivation

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId VarId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem protected_receiver_alias_requires_mutable_root (config : EvalConfig) (initialized : Nat)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (region : ReceivingRegion)
    (root : RootInst) (stored : StoredValue) (incoming : Nat)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (regionMember : region ∈ regions) (receiver : region.destination = incoming)
    (retained : live root) (value : state.objects.lookup root = some (.stored stored))
    (alias : stored.destination = some incoming) : region.mutableRoots root := by
  by_cases mutable : region.mutableRoots root
  · exact mutable
  · have protection := world.protections region regionMember
    have allowed : incoming ∈ region.mutableDestinations := by simpa only [receiver] using protection.authority
    exact False.elim (protection.names root retained mutable (.stored stored) value stored (.stored stored) incoming alias allowed)

theorem protected_published_alias_fault_requires_mutable_root (config : EvalConfig) (initialized : Nat)
    (source : RuntimeActivation) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (region : ReceivingRegion) (token incoming count : Nat) (snapshot : PendingDestination)
    (localVar : VarId) (origin : OriginId) (root : RootInst) (stored : StoredValue)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (regionMember : region ∈ regions) (receiver : region.destination = incoming) (retained : live root)
    (waiting : state.construction.exitReservations[token]? = some (.waiting incoming))
    (present : state.construction.destinations[incoming]? = some snapshot) (published : snapshot.progress = .published count)
    (current : destinationCurrent state.construction incoming = .ok incoming)
    (rooted : rootOf source localVar state = .ok root state)
    (value : state.objects.lookup root = some (.stored stored)) (alias : stored.destination = some incoming) :
    region.mutableRoots root ∧ ∃ activated,
      selectCompletionChannel source (.resultLocal localVar origin) (.completion token) state = .ok (.construct incoming) activated ∧
      prepareNamedCarrierAt origin token incoming stored activated = .stop (.fault .flow) activated := by
  exact ⟨protected_receiver_alias_requires_mutable_root config initialized state ambient types live regions pending region root stored incoming
      world regionMember receiver retained value alias,
    published_alias_select_then_prepare_fault source state token incoming count snapshot localVar origin root stored waiting present published current rooted value alias⟩

#print axioms protected_receiver_alias_requires_mutable_root
#print axioms protected_published_alias_fault_requires_mutable_root

end Goose.Proofs.ConstructionAcceptedExecution
