import Goose.Proofs.ConstructionAcceptedBytePublication

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation

theorem publish_direct_packed_success (origin : Goose.Core.OriginId) (state : ExecutionState)
    (id storageId count : Nat) (row : PendingDestination) (storage : ReceivingStorage)
    (present : state.construction.destinations[id]? = some row)
    (stored : state.construction.storage[storageId]? = some storage)
    (progress : row.progress = .built count) (receiver : row.use = .receiver)
    (backing : row.backing = .direct storageId) (storageEq : row.storage = storageId)
    (packed : row.layout = .packed) (adaptation : row.adaptation = none) (fits : count < 2 ^ 32) :
    ∃ after, publishCarriers origin [.completed id] state = .ok () after := by
  have checked := preflightPublication_direct_packed state.construction id storageId count row storage
    present stored progress receiver backing storageEq packed adaptation fits
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  simp only [publishCarriers, List.mapM_cons, List.mapM_nil, bind, pure, List.filterMap_cons,
    List.filterMap_nil, _root_.id, liftConstruction, publishOperation, ConstructionM.get, checked,
    List.forIn_cons, List.forIn_nil, publishReady_transition, lookupDestination_result, present, progress,
    receiver, backing, DestinationBacking.receiverStorage, lookupStorage_result, stored, packed,
    replaceStorage_result, replaceDestination_result, storageInside, inside, ↓reduceIte, emit_result]
  exact ⟨_, rfl⟩

#print axioms publish_direct_packed_success
end Goose.Proofs.ConstructionAcceptedExecution
