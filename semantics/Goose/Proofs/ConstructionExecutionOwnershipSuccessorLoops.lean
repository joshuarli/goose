import Goose.Proofs.ConstructionExecutionOwnershipSuccessorMap

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

theorem framesSuccessorMap_listForIn (items : List α) (initial : β)
    (action : α → β → ConstructionM (ForInStep β))
    (preserved : ∀ item value, FramesSuccessorMap (action item value)) :
    FramesSuccessorMap (forIn items initial action) := by
  induction items generalizing initial with
  | nil => exact framesSuccessorMap_pure _
  | cons item rest ih =>
      rw [List.forIn_cons]
      apply framesSuccessorMap_bind
      · exact preserved item initial
      · intro step
        cases step with
        | done value => exact framesSuccessorMap_pure value
        | yield value => exact ih value

abbrev protectedDiscard (rows : List PendingDestination) : ConstructionM Unit :=
  protected_abandonment_head rows

theorem protectedDiscard_cleanup (rows : List PendingDestination) :
    protectedDiscard rows = protectedCleanup rows := by
  funext state
  induction rows generalizing state with
  | nil => rfl
  | cons row rest ih =>
      simp only [protectedDiscard, protectedAbandonment_cons_transition, protectedCleanup_cons]

theorem protectedDiscard_successorMap (rows : List PendingDestination) :
    FramesSuccessorMap (protectedDiscard rows) := by
  rw [protectedDiscard_cleanup]
  exact framesSuccessorMap_of_frame _ (protectedCleanup_successorFrame rows)

theorem abandonPreservingExit_successorMap (id replacement : DestinationId) :
    FramesSuccessorMap (abandonPreservingExit id replacement) := by
  unfold abandonPreservingExit
  apply framesSuccessorMap_bind
  · exact framesSuccessorMap_of_frame _ framesSuccessors_get
  · intro state
    split
    · exact framesSuccessorMap_fail _
    · exact protectedDiscard_successorMap _

abbrev readyPublish (id : DestinationId) : ConstructionM Unit :=
  (fun {left right : ConstructionM Unit} (_ : left = right) => left) (publishReady_transition id)

set_option maxHeartbeats 800000 in
theorem readyPublish_successorMap (id : DestinationId) : FramesSuccessorMap (readyPublish id) := by
  simp only [readyPublish, publishReady_transition]
  apply framesSuccessorMap_bind (destinationLookup id)
  · exact framesSuccessorMap_of_frame _ (destinationLookup_successorFrame id)
  · intro destination
    try dsimp (config := { zeta := true, zetaHave := true }) only
    successor_map

theorem publishOperation_successorMap (ids : List DestinationId) :
    FramesSuccessorMap (publishOperation ids) := by
  unfold publishOperation
  apply framesSuccessorMap_bind
  · exact framesSuccessorMap_of_frame _ framesSuccessors_get
  · intro state
    split
    · exact framesSuccessorMap_fail _
    · apply framesSuccessorMap_bind
      · apply framesSuccessorMap_listForIn
        intro id value
        apply framesSuccessorMap_bind
        · exact readyPublish_successorMap id
        · intro published
          exact framesSuccessorMap_pure _
      · intro finished
        exact framesSuccessorMap_pure _

end Goose.Proofs.ConstructionExecutionOwnership
