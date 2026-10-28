import Goose.Proofs.ConstructionAcceptedRegionLimits

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (ActId ConstructionRequest OriginId RootInst)
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem newDestination_publishedOwner_storage (config : EvalConfig) (initialized : Nat)
    (owner : ActId) (ty : Ty) (request : ConstructionRequest) (origin : OriginId) (knownCount : Option Nat)
    (before allocated final : ExecutionState) (id count : Nat) (row : PendingDestination) (stored : StoredValue)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout owner ty request origin none knownCount before = .ok id allocated)
    (history : OwnershipSourceExtension allocated.construction final.construction)
    (present : final.construction.destinations[id]? = some row) (published : row.progress = .published count)
    (sampled : storedDestination id final = .ok stored final) :
    stored.storage = before.construction.storage.size ∧ stored.destination = some id := by
  obtain ⟨frame⟩ := newDestination_fresh_frame config.layout owner ty request origin knownCount before allocated id
    world.ownership.source.structural.1.1.1 created
  obtain ⟨original, originalPresent, receiverStorage, fresh⟩ :=
    newDestination_success_fresh config.layout owner ty request origin knownCount before allocated id created
  have idFresh := newDestination_fresh_id config.layout owner ty request origin knownCount before allocated id created
  have framePresent : allocated.construction.destinations[id]? = some frame.row := by
    rw [frame.destinations, idFresh]
    simp only [Array.getElem?_push_size]
  have same : original = frame.row := Option.some.inj (originalPresent.symm.trans framePresent)
  have receiver : original.use = .receiver := by rw [same]; exact frame.receiver
  obtain ⟨current, found, use, storage⟩ := history.receiverStorage allocated.construction final.construction id
    original originalPresent receiver
  have sameCurrent : current = row := Option.some.inj (found.symm.trans present)
  subst current
  simp only [storedDestination, getDestination, EvalM.get, present, bind, pure, published, progressCount] at sampled
  cases sampled
  exact ⟨storage.trans receiverStorage, rfl⟩

#print axioms newDestination_publishedOwner_storage

end Goose.Proofs.ConstructionAcceptedExecution
