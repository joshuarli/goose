import Goose.Proofs.ConstructionExecutionOwnershipSuccessorMap

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

theorem framesSuccessorMap_get_set (update : ConstructionState → ConstructionState)
    (next : ConstructionState → ConstructionM α)
    (unchanged : ∀ state, (update state).destinationSuccessors = state.destinationSuccessors)
    (remaining : ∀ state, FramesSuccessorMap (next state)) :
    FramesSuccessorMap (do
      let state ← ConstructionM.get
      ConstructionM.set (update state)
      next state) := by
  intro state
  simpa only [ConstructionM.get, ConstructionM.set, bind] using
    (remaining state (update state)).trans (unchanged state)

theorem constructionM_bind_pure (value : α) (next : α → ConstructionM β) :
    (pure value : ConstructionM α) >>= next = next value := rfl

theorem constructionM_bind_fail (reason : ConstructionFault) (next : α → ConstructionM β) :
    (ConstructionM.fail reason : ConstructionM α) >>= next = ConstructionM.fail reason := rfl

open Lean Elab Term Meta in
elab "allocation_available_head" : term => do
  let info ← getConstInfo ``Goose.Construct.openChild
  let some value := info.value? | throwError "missing child definition"
  let some head := value.find? (fun term => match term with
    | .const name _ => name.toString.endsWith ".writingAvailable"
    | _ => false) | throwError "missing availability query"
  pure head

abbrev allocationAvailable : PendingDestination → ReceivingStorage → Nat → Bool := allocation_available_head

abbrev allocationPrefix : ReceivingLayout → ConstructionRequest → Bool := renewal_prefix_test

set_option maxHeartbeats 800000 in
theorem openExitReplacement_successorMap (id : DestinationId) :
    FramesSuccessorMap (openExitReplacement id) := by
  unfold openExitReplacement
  apply framesSuccessorMap_bind (writableLookup id)
  · exact writableLookup_successorMap id
  · intro destination
    cases progress : destination.progress
    all_goals simp only [progress, constructionM_bind_pure, constructionM_bind_fail]
    all_goals try exact framesSuccessorMap_fail _
    all_goals
      apply framesSuccessorMap_bind (storageLookup destination.storage)
      · exact framesSuccessorMap_of_frame _ (storageLookup_successorFrame _)
      · intro storage
        try dsimp (config := { zeta := true, zetaHave := true }) only
        apply framesSuccessorMap_get_set (fun state => { state with destinations := state.destinations.push (⟨{ destination.capability with id := state.destinations.size, start := storage.bytes.size },
            destination.backing, destination.layout, .replacement id, .open 0,
            storage.bytes.size + (if allocationPrefix destination.layout destination.capability.request then 4 else 0),
            storage.bytes.size, none, destination.adaptation⟩) })
        · intro state; rfl
        · intro state
          successor_map

set_option maxHeartbeats 800000 in
theorem openChild_successorMap (parent : DestinationId) (ty : Goose.Construct.Ty)
    (layout : ReceivingLayout) : FramesSuccessorMap (openChild parent ty layout) := by
  unfold openChild
  apply framesSuccessorMap_bind (writableLookup parent)
  · exact writableLookup_successorMap parent
  · intro destination
    cases progress : destination.progress
    all_goals simp only [progress]
    all_goals try exact framesSuccessorMap_fail _
    case «open» count =>
      apply framesSuccessorMap_bind (storageLookup destination.storage)
      · exact framesSuccessorMap_of_frame _ (storageLookup_successorFrame _)
      · intro storage
        by_cases full : (!allocationAvailable destination storage (count + 1)) = true
        · dsimp only [allocationAvailable] at full
          simp only [full, ↓reduceIte, constructionM_bind_fail]
          exact framesSuccessorMap_fail _
        · dsimp only [allocationAvailable] at full
          simp only [full, ↓reduceIte, constructionM_bind_pure]
          apply framesSuccessorMap_get_set (fun state => { state with destinations := state.destinations.push (⟨{ destination.capability with id := state.destinations.size, layout := ty, logicalType := ty, request := .value, start := destination.writeEnd },
              .direct destination.storage, layout, .child parent, .open 0,
              destination.writeEnd + (if allocationPrefix layout .value then 4 else 0),
              (match destination.layout with | .limited _ _ => storage.bytes.size | _ => destination.writeEnd),
              none, none⟩) })
          · intro state; rfl
          · intro state
            successor_map

end Goose.Proofs.ConstructionExecutionOwnership
