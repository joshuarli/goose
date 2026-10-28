import Goose.Proofs.ConstructionExitLandingReceiverChildren
import Goose.Proofs.ExitExecutionCommitLanding

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem commit_receiver_landing_child_invariants (state : ConstructionState)
    (id count anchorId : Nat) (replacement anchor : PendingDestination) (storage : ReceivingStorage)
    (receiving : Option DestinationId) (chain : List DestinationId)
    (lifecycle : DestinationLifecycleInvariant state)
    (unique : ActiveChildUnique state) (blocked : ActiveChildParentBlocked state)
    (checked : ∃ rows, protectedExitDiscarded state anchorId id = .ok rows)
    (present : state.destinations[id]? = some replacement) (built : replacement.progress = .built count)
    (stored : state.storage[replacement.storage]? = some storage)
    (selected : exitLandingAnchor (state.destinations.size + 1) id replacement.storage receiving state =
      .ok (anchorId, anchor, chain) state)
    (receiver : anchor.use = .receiver)
    (startOrder : anchor.capability.start ≤ replacement.capability.start)
    (inside : replacement.capability.start ≤ storage.bytes.size) :
    ∃ after, commitExitReplacement receiving id state = .ok () after ∧
      ActiveChildUnique after ∧ ActiveChildParentBlocked after := by
  obtain ⟨update, executed, bounded, different, footprint, ready⟩ :=
    commitExitReplacement_of_anchor state id count replacement storage receiving anchorId anchor chain lifecycle
      present built stored selected (.receiver receiver) startOrder inside
  have noUpdate : update = none := by
    cases update with
    | none => rfl
    | some pair =>
      obtain ⟨parentId, parent⟩ := pair
      have use := footprint parentId parent rfl
      rcases use with child | replacement
      · rw [receiver] at child
        cases child
      · rw [receiver] at replacement
        cases replacement
  subst update
  refine ⟨committedExitState state id anchorId count replacement anchor storage none chain, executed, ?_⟩
  have candidates := completed_receiver_landing_child_invariants state id anchorId count replacement anchor storage
    lifecycle.2.1 lifecycle.2.2.2 unique blocked checked present built receiver
  simpa only [committedExitState, ActiveChildUnique, ActiveChildParentBlocked] using candidates

#print axioms commit_receiver_landing_child_invariants

end Goose.Proofs.ConstructionAcceptedExecution
