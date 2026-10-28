import Goose.Proofs.ConstructionAcceptedByteAllocation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation

theorem publish_direct_packed_backing (layout : LayoutEnv) (origin : Goose.Core.OriginId)
    (id storageId count : Nat) (before after : ExecutionState)
    (destination : PendingDestination) (storage : ReceivingStorage)
    (present : before.construction.destinations[id]? = some destination)
    (stored : before.construction.storage[storageId]? = some storage)
    (backing : destination.backing = .direct storageId)
    (progress : destination.progress = .built count) (use : destination.use = .receiver)
    (packed : destination.layout = .packed)
    (interval : SampledRunBacking layout storage.bytes
      ⟨destination.capability.start + (if destination.layout == .packed && destination.capability.request == .value then 4 else 0),
        count, .int .u8⟩)
    (ty : destination.capability.logicalType = .varr (.int .u8))
    (executed : publishCarriers origin [.completed id] before = .ok () after) :
    ∃ value, storedDestination id after = .ok value after ∧ StoredValueBacking layout after value := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  simp only [publishCarriers, List.mapM_cons, List.mapM_nil, bind, pure, List.filterMap_cons,
    List.filterMap_nil, _root_.id, liftConstruction] at executed
  simp only [publishOperation, ConstructionM.get, bind] at executed
  cases checked : preflightPublication before.construction [id] with
  | error reason => simp only [checked, ConstructionM.fail] at executed; cases executed
  | ok result =>
    cases result
    simp only [checked, List.forIn_cons, List.forIn_nil, bind, pure, publishReady_transition,
      lookupDestination_result, present, progress, use, backing, DestinationBacking.receiverStorage,
      lookupStorage_result, stored, packed, replaceStorage_result, replaceDestination_result,
      storageInside, inside, ↓reduceIte, emit_result, ExecutionStep.ok.injEq,
      true_and] at executed
    subst after
    let published := { destination with progress := .published count, backing := .direct storageId, writeEnd := destination.capability.start + (destination.writeEnd - destination.capability.start) }
    let value : StoredValue := ⟨storageId, destination.capability.start, .varr (.int .u8), count, some id, none, [], count⟩
    have row : (before.construction.destinations.set! id published)[id]? = some published :=
      Array.getElem?_setIfInBounds_self_of_lt inside
    have bytes : (before.construction.storage.set! storageId { storage with publishedCount := count })[storageId]? =
        some { storage with publishedCount := count } := Array.getElem?_setIfInBounds_self_of_lt storageInside
    refine ⟨value, ?_, ?_⟩
    · simp [storedDestination, getDestination, EvalM.get, bind, pure,
        inside, DestinationBacking.receiverStorage,
        progressCount, ty, value]
    · refine .named id { storage with publishedCount := count } published count bytes rfl ?_ ?_ ?_ ?_ ?_
        (.int .u8) rfl ?_
      · simpa only [published, packed, use, backing] using row
      · rfl
      · simpa only [published, value] using ty.symm
      · rfl
      · rfl
      · simpa [published, value, storedWrittenRun, packed] using interval

#print axioms publish_direct_packed_backing

end Goose.Proofs.ConstructionAcceptedExecution
