import Goose.Proofs.ConstructionExitInactiveChildLanding

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionProtocol

theorem suspended_parent_rejects_child_allocation (state : ConstructionState)
    (parent count expected : Nat) (row : PendingDestination)
    (present : state.destinations[parent]? = some row) (suspended : row.progress = .suspended count expected)
    (ty : Goose.Construct.Ty) (layout : ReceivingLayout) (known : Option Nat) (request : ConstructionRequest)
    (location : Loc) :
    openChild parent ty layout state = .fault .protocol state ∧
    openExtension parent request known state = .fault .protocol state ∧
    openElementExtension parent ty layout known location state = .fault .protocol state := by
  cases allowed : destinationCanWrite state parent <;>
    simp [openChild, openExtension, openElementExtension, writableDestination_result,
      present, allowed, suspended, bind, ConstructionM.fail]

theorem retargeted_parent_rejects_child_anchor_commit (state : ConstructionState)
    (id count old parentId parentCount expected : Nat) (replacement anchor parent : PendingDestination)
    (receiving : Option DestinationId) (chain : List DestinationId)
    (present : state.destinations[id]? = some replacement) (built : replacement.progress = .built count)
    (selected : exitLandingAnchor (state.destinations.size + 1) id replacement.storage receiving state =
      .ok (old, anchor, chain) state)
    (anchorUse : anchor.use = .child parentId) (parentFound : state.destinations[parentId]? = some parent)
    (parentPhase : parent.progress = .suspended parentCount expected) (different : expected ≠ old) :
    commitExitReplacement receiving id state = .fault .ownership state := by
  have mismatch : (expected != old) = true := bne_iff_ne.mpr different
  simp only [commitExitReplacement, lookupDestination_result, present, built, ConstructionM.get, selected,
    anchorUse, parentFound, parentPhase, mismatch, ↓reduceIte, bind, pure, ConstructionM.fail]

#print axioms retargeted_parent_rejects_child_anchor_commit
#print axioms suspended_parent_rejects_child_allocation

end Goose.Proofs.ConstructionAcceptedExecution
