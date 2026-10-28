import Goose.Proofs.ConstructionExitNamedPrepareWorld

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem accepted_named_built_geometry (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (root : RootInst)
    (incoming count : Nat) (stored : StoredValue) (row : PendingDestination)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (retained : live root) (value : state.objects.lookup root = some (.stored stored))
    (alias : stored.destination = some incoming) (present : state.construction.destinations[incoming]? = some row)
    (built : row.progress = .built count) :
    ∃ storage, state.construction.storage[row.storage]? = some storage ∧
      row.storage = stored.storage ∧ row.capability.start = stored.start ∧
      stored.ty.adaptsTo row.capability.logicalType = true := by
  have backedValue := world.backing.values root retained (.stored stored) value
  cases backedValue with
  | stored stored backed =>
    cases backed with
    | detached storage element storageFound detached ty interval =>
      rw [alias] at detached
      cases detached
    | named id storage destination oldCount storageFound named binding backing ty start progress element elementType interval =>
      have sameId : id = incoming := Option.some.inj (named.symm.trans alias)
      subst id
      have sameRow : destination = row := Option.some.inj (binding.symm.trans present)
      subst destination
      have sameStorage : stored.storage = row.storage := by simpa only [built] using backing
      refine ⟨storage, ?_, sameStorage.symm, start.symm, ?_⟩
      · simpa only [sameStorage] using storageFound
      · rw [ty]
        simp [Ty.adaptsTo]

theorem accepted_named_built_prepare_world (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (initial state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (origin : Goose.Core.OriginId) (receipt : BorrowedWaitingExitReservation) (count : Nat)
    (snapshot row : PendingDestination) (stored : StoredValue) (root : RootInst)
    (oldWorld : AcceptedWorld config initialized initial ambient types live regions pending)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (captured : receipt ∈ Goose.Proofs.ExitExecution.borrowedExitChannelReceipts activation initial)
    (current : destinationCurrent state.construction receipt.incoming = .ok receipt.incoming)
    (ticket : state.construction.exitReservations[receipt.token]? = some (.active (.named .awaitingSource) receipt.incoming receipt.incoming snapshot))
    (present : state.construction.destinations[receipt.incoming]? = some row) (built : row.progress = .built count)
    (retained : live root) (value : state.objects.lookup root = some (.stored stored))
    (alias : stored.destination = some receipt.incoming) (sameCount : count = stored.count)
    (startBound : row.capability.start ≤ row.writeEnd)
    (endBound : ∀ storage, state.construction.storage[row.storage]? = some storage → row.writeEnd ≤ storage.bytes.size) :
    ∃ after, prepareNamedCarrierAt origin receipt.token receipt.incoming stored state = .ok (some (.pendingNamed receipt.token)) after ∧
      AcceptedWorld config initialized after ambient types live regions pending := by
  obtain ⟨storage, found, sameStorage, sameStart, type⟩ := accepted_named_built_geometry config initialized state ambient types live regions pending root
    receipt.incoming count stored row world retained value alias present built
  exact prepareNamedCarrierAt_built_world config initialized activation initial state ambient types live regions pending origin receipt count
    snapshot row storage stored oldWorld world captured current ticket present built found alias sameStorage sameStart type sameCount startBound (endBound storage found)

#print axioms accepted_named_built_prepare_world
#print axioms accepted_named_built_geometry

end Goose.Proofs.ConstructionAcceptedExecution
