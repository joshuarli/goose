import Goose.Proofs.ConstructionExitDirectResumption

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem renew_abandoned_child_retargets_parent (state final : ConstructionState)
    (incoming current parentId count selected : Nat)
    (row snapshot parent : PendingDestination) (storage : ReceivingStorage)
    (resolved : destinationCurrent state incoming = .ok current)
    (present : state.destinations[current]? = some row) (inactive : row.progress = .abandoned)
    (saved : state.destinationResumptions.lookup current = some snapshot)
    (adaptation : snapshot.adaptation = none) (layout : snapshot.layout = .elements)
    (use : snapshot.use = .child parentId) (stored : state.storage[snapshot.storage]? = some storage)
    (start : snapshot.capability.start ≤ storage.bytes.size)
    (parentFound : state.destinations[parentId]? = some parent)
    (parentPhase : parent.progress = .suspended count current)
    (executed : renewReceivingDestination incoming state = .ok selected final) :
    selected = state.destinations.size ∧
      final.destinations[parentId]? = some { parent with progress := .suspended count selected } := by
  have parentInside := (Array.getElem?_eq_some_iff.mp parentFound).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  simp only [renewReceivingDestination, ConstructionM.get, resolved, lookupDestination_result, present,
    inactive, saved, lookupStorage_result, stored, adaptation, bind, pure] at executed
  simp only [show ¬ storage.bytes.size < snapshot.capability.start from Nat.not_lt.mpr start,
    Bool.false_eq_true, ↓reduceIte, use, parentFound, parentPhase, bne_self_eq_false, bind, pure,
    ConstructionM.set, replaceDestination_result, replaceStorage_result, emit_result,
    Array.size_push, Nat.lt_succ_of_lt parentInside, storageInside, Array.size_setIfInBounds] at executed
  simp [layout, hasPrefix_result, bind, pure] at executed
  cases backing : snapshot.backing <;>
    simp [backing, bind, pure, ConstructionResult.ok.injEq] at executed <;>
    obtain ⟨same, rfl⟩ := executed <;>
    subst selected <;>
    simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self, Nat.lt_succ_of_lt parentInside]


theorem renewed_child_blocks_old_anchor_commit (state final : ConstructionState)
    (incoming current parentId count selected resultId resultCount : Nat)
    (row snapshot parent replacement anchor : PendingDestination) (storage : ReceivingStorage)
    (receiving : Option DestinationId) (chain : List DestinationId)
    (resolved : destinationCurrent state incoming = .ok current)
    (present : state.destinations[current]? = some row) (inactive : row.progress = .abandoned)
    (saved : state.destinationResumptions.lookup current = some snapshot)
    (adaptation : snapshot.adaptation = none) (layout : snapshot.layout = .elements)
    (use : snapshot.use = .child parentId) (stored : state.storage[snapshot.storage]? = some storage)
    (start : snapshot.capability.start ≤ storage.bytes.size)
    (parentFound : state.destinations[parentId]? = some parent) (parentPhase : parent.progress = .suspended count current)
    (renewed : renewReceivingDestination incoming state = .ok selected final)
    (replacementFound : final.destinations[resultId]? = some replacement) (built : replacement.progress = .built resultCount)
    (anchorFound : exitLandingAnchor (final.destinations.size + 1) resultId replacement.storage receiving final =
      .ok (current, anchor, chain) final) (anchorUse : anchor.use = .child parentId) :
    commitExitReplacement receiving resultId final = .fault .ownership final := by
  obtain ⟨fresh, newParent⟩ := renew_abandoned_child_retargets_parent state final incoming current parentId count selected
    row snapshot parent storage resolved present inactive saved adaptation layout use stored start parentFound parentPhase renewed
  have currentInside := (destinationCurrent_bounds state incoming current resolved).2
  have different : selected ≠ current := by rw [fresh]; exact Ne.symm (Nat.ne_of_lt currentInside)
  exact retargeted_parent_rejects_child_anchor_commit final resultId resultCount current parentId count selected
    replacement anchor { parent with progress := .suspended count selected } receiving chain replacementFound built anchorFound
    anchorUse newParent rfl different

#print axioms renewed_child_blocks_old_anchor_commit
#print axioms renew_abandoned_child_retargets_parent

end Goose.Proofs.ConstructionAcceptedExecution
