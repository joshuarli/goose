import Goose.Proofs.ConstructionExitNamedBackingGeometry

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem storedDestination_built_count (state : ExecutionState) (incoming count : Nat)
    (row : PendingDestination) (stored : StoredValue)
    (present : state.construction.destinations[incoming]? = some row)
    (built : row.progress = .built count)
    (sampled : storedDestination incoming state = .ok stored state) : stored.count = count := by
  simp only [storedDestination, getDestination, EvalM.get, present, bind, built, progressCount, pure,
    ExecutionStep.ok.injEq] at sampled
  obtain ⟨same, _⟩ := sampled
  cases same
  rfl

theorem accepted_sampled_named_prepare_world (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (initial state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (origin : OriginId) (receipt : BorrowedWaitingExitReservation) (count : Nat)
    (snapshot row : PendingDestination) (stored : StoredValue) (root : RootInst)
    (oldWorld : AcceptedWorld config initialized initial ambient types live regions pending)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (captured : receipt ∈ Goose.Proofs.ExitExecution.borrowedExitChannelReceipts activation initial)
    (current : destinationCurrent state.construction receipt.incoming = .ok receipt.incoming)
    (ticket : state.construction.exitReservations[receipt.token]? = some (.active (.named .awaitingSource) receipt.incoming receipt.incoming snapshot))
    (present : state.construction.destinations[receipt.incoming]? = some row) (built : row.progress = .built count)
    (retained : live root) (value : state.objects.lookup root = some (.stored stored))
    (alias : stored.destination = some receipt.incoming)
    (sampled : storedDestination receipt.incoming state = .ok stored state)
    (startBound : row.capability.start ≤ row.writeEnd)
    (endBound : ∀ storage, state.construction.storage[row.storage]? = some storage → row.writeEnd ≤ storage.bytes.size) :
    ∃ after, prepareNamedCarrierAt origin receipt.token receipt.incoming stored state = .ok (some (.pendingNamed receipt.token)) after ∧
      AcceptedWorld config initialized after ambient types live regions pending := by
  have countEq := storedDestination_built_count state receipt.incoming count row stored present built sampled
  exact accepted_named_built_prepare_world config initialized activation initial state ambient types live regions pending origin receipt count
    snapshot row stored root oldWorld world captured current ticket present built retained value alias countEq.symm startBound endBound

#print axioms storedDestination_built_count
#print axioms accepted_sampled_named_prepare_world

end Goose.Proofs.ConstructionAcceptedExecution
