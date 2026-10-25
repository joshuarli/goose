import Goose.Proofs.ConstructionExecutionOwnershipSuccessorAllocation

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

abbrev receivingPrefixBytes : ByteArray := renewal_prefix_bytes

theorem storageLookup_get_commute (id : StorageId)
    (next : ConstructionState → ReceivingStorage → ConstructionM α) :
    (do let state ← ConstructionM.get; let storage ← storageLookup id; next state storage) =
    (do let storage ← storageLookup id; let state ← ConstructionM.get; next state storage) := by
  funext state
  simp only [ConstructionM.get, bind, storageLookup, lookupStorage_result]
  cases state.storage[id]? <;> rfl

private theorem receivingAllocation_successorMap (capability : Destination Goose.Construct.Ty)
    (layout : ReceivingLayout) (known : Option Nat) (backing : DestinationBacking) :
    FramesSuccessorMap (do
      let state ← ConstructionM.get
      let storage ← storageLookup backing.writeStorage
      let id := state.destinations.size
      let start := match layout, backing with
        | .limited _ slotBytes, .direct _ => storage.publishedCount * slotBytes
        | _, _ => storage.bytes.size
      if start > storage.bytes.size then ConstructionM.fail .storage
      let capability := { capability with id := id, start := start }
      let row : PendingDestination := ⟨capability, backing, layout, .receiver, .open 0,
        start + (if allocationPrefix layout capability.request then 4 else 0),
        (match layout with | .limited _ _ => storage.bytes.size | _ => start), known, none⟩
      ConstructionM.set { state with destinations := state.destinations.push row }
      if allocationPrefix layout capability.request then
        storageReplace backing.writeStorage { storage with bytes := storage.bytes ++ receivingPrefixBytes }
      eventEmit (.begin id)
      match backing with | .staged _ _ => eventEmit (.stage id) | .direct _ => pure ()
      pure id) := by
  rw [storageLookup_get_commute]
  apply framesSuccessorMap_bind (storageLookup backing.writeStorage)
  · exact framesSuccessorMap_of_frame _ (storageLookup_successorFrame _)
  · intro storage
    let start := match layout, backing with
      | .limited _ slotBytes, .direct _ => storage.publishedCount * slotBytes
      | _, _ => storage.bytes.size
    by_cases beyond : start > storage.bytes.size
    · dsimp only [start] at beyond
      simp (config := { zeta := true, zetaHave := true }) only [beyond, ↓reduceIte, constructionM_bind_fail]
      apply framesSuccessorMap_bind
      · exact framesSuccessorMap_of_frame _ framesSuccessors_get
      · intro state; exact framesSuccessorMap_fail _
    · dsimp only [start] at beyond
      simp (config := { zeta := true, zetaHave := true }) only [beyond, ↓reduceIte, constructionM_bind_pure]
      cases layout <;> cases backing
      all_goals simp (config := { zeta := true, zetaHave := true }) only [↓reduceIte] at *
      all_goals
        apply framesSuccessorMap_get_set
        · intro state; rfl
        · intro state; successor_map

syntax "successor_receiving" : tactic
macro_rules
| `(tactic| successor_receiving) => `(tactic|
  first
  | exact receivingAllocation_successorMap _ _ _ _
  | exact reserveStorage_successorMap _ _
  | exact framesSuccessorMap_of_frame _ framesSuccessors_get
  | exact framesSuccessorMap_pure _
  | exact framesSuccessorMap_fail _
  | exact framesSuccessorMap_of_frame _ (storageLookup_successorFrame _)
  | (apply framesSuccessorMap_bind
     · successor_receiving
     · intro value; successor_receiving)
  | (split <;> successor_receiving))

set_option maxHeartbeats 800000 in
theorem openDestination_successorMap (storage : StorageId) (capability : Destination Goose.Construct.Ty)
    (layout : ReceivingLayout) (known : Option Nat) :
    FramesSuccessorMap (openDestination storage capability layout known) := by
  rw [openDestination_transition]
  apply framesSuccessorMap_bind (storageLookup storage)
  · exact framesSuccessorMap_of_frame _ (storageLookup_successorFrame _)
  · intro receiving
    try dsimp (config := { zeta := true, zetaHave := true }) only
    successor_receiving

set_option maxHeartbeats 800000 in
theorem openDestinationDirect_successorMap (storage : StorageId) (capability : Destination Goose.Construct.Ty)
    (layout : ReceivingLayout) (known : Option Nat) :
    FramesSuccessorMap (openDestinationDirect storage capability layout known) := by
  rw [openDestinationDirect_transition]
  apply framesSuccessorMap_bind (storageLookup storage)
  · exact framesSuccessorMap_of_frame _ (storageLookup_successorFrame _)
  · intro receiving
    try dsimp (config := { zeta := true, zetaHave := true }) only
    successor_receiving

end Goose.Proofs.ConstructionExecutionOwnership
