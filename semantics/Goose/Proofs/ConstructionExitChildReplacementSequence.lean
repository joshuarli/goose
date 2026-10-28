import Goose.Proofs.ConstructionExitLandingChildAnchor
import Goose.Proofs.ConstructionExitChildWrite

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem child_replacement_finish_commit_preserves_candidates
    (before opened finished : ConstructionState) (child replacement count replacementCount : Nat)
    (parentId parentCount : Nat) (childRow replacementRow parent anchor : PendingDestination)
    (initialStorage landingStorage : ReceivingStorage) (receiving : Option DestinationId) (chain : List DestinationId)
    (childFound : before.destinations[child]? = some childRow) (childOpen : childRow.progress = .open count)
    (childStorage : before.storage[childRow.storage]? = some initialStorage)
    (ordered : DestinationOwnersOrdered before) (unique : ActiveChildUnique before) (blocked : ActiveChildParentBlocked before)
    (openedResult : openExitReplacement child before = .ok replacement opened)
    (replacementFound : opened.destinations[replacement]? = some replacementRow)
    (replacementOpen : replacementRow.progress = .open replacementCount)
    (packed : replacementRow.layout = .packed) (request : replacementRow.capability.request = .value)
    (finishResult : finishDestination replacement opened = .ok () finished)
    (lifecycle : DestinationLifecycleInvariant finished)
    (checked : ∃ rows, protectedExitDiscarded finished child replacement = .ok rows)
    (stored : finished.storage[replacementRow.storage]? = some landingStorage)
    (selected : exitLandingAnchor (finished.destinations.size + 1) replacement replacementRow.storage receiving finished =
      .ok (child, anchor, chain) finished)
    (anchorUse : anchor.use = .child parentId)
    (parentFound : finished.destinations[parentId]? = some parent)
    (parentPhase : parent.progress = .suspended parentCount child)
    (startOrder : anchor.capability.start ≤ replacementRow.capability.start)
    (inside : replacementRow.capability.start ≤ landingStorage.bytes.size) :
    anchor.progress = .exiting count replacement ∧
    ∃ after, commitExitReplacement receiving replacement finished = .ok () after ∧
      ActiveChildUnique after ∧ ActiveChildParentBlocked after := by
  have openedUnique := open_replacement_preserves_unique_children before opened child replacement count childRow initialStorage
    childFound childOpen childStorage unique openedResult
  have openedBlocked := open_replacement_preserves_blocked_children before opened child replacement count childRow initialStorage
    childFound childOpen childStorage ordered blocked openedResult
  have finishedCandidates := finish_packed_preserves_child_invariants opened finished replacement replacementCount replacementRow
    replacementFound replacementOpen packed request openedUnique openedBlocked finishResult
  have fresh := open_replacement_fresh before opened child replacement count childRow initialStorage
    childFound childOpen childStorage openedResult
  have childInside := (Array.getElem?_eq_some_iff.mp childFound).1
  have different : child ≠ replacement := by rw [fresh]; exact Nat.ne_of_lt childInside
  have parentRow := open_replacement_parent_exact before opened child replacement count childRow childFound childOpen openedResult
  have parentUnchanged := finish_packed_byte_other_row opened finished replacement child replacementCount replacementRow
    replacementFound replacementOpen packed request different finishResult
  obtain ⟨_, _, anchorFound⟩ := exitLandingAnchor_success _ _ _ _ finished finished child anchor chain selected
  have sameAnchor : { childRow with progress := .exiting count replacement } = anchor := by
    apply Option.some.inj
    exact (parentUnchanged.trans parentRow).symm.trans anchorFound
  refine ⟨?_, ?_⟩
  · rw [← sameAnchor]
  have builtFound := finish_packed_byte_row opened finished replacement replacementCount replacementRow
    replacementFound replacementOpen packed request finishResult
  apply commit_child_landing_child_invariants finished replacement child replacementCount parentId parentCount
    { replacementRow with progress := .built replacementCount } anchor parent landingStorage receiving chain lifecycle
    finishedCandidates.1 finishedCandidates.2 checked builtFound rfl
  · simpa only [PendingDestination.storage] using stored
  · simpa only [PendingDestination.storage] using selected
  · exact anchorUse
  · exact parentFound
  · exact parentPhase
  · simpa only using startOrder
  · simpa only using inside

#print axioms child_replacement_finish_commit_preserves_candidates

end Goose.Proofs.ConstructionAcceptedExecution
