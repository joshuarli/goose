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


theorem renew_abandoned_child_successor (state final : ConstructionState)
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
    selected = state.destinations.size ∧ final.destinations.size = state.destinations.size + 1 ∧
      final.destinationSuccessors = (current, selected) :: state.destinationSuccessors ∧
      ∃ row, final.destinations[selected]? = some row ∧ row.progress = .open 0 := by
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
    simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne,
      Nat.ne_of_lt parentInside, Array.getElem?_push]


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

theorem renew_abandoned_child_resolves_to_fresh (state final : ConstructionState)
    (incoming current parentId count selected : Nat)
    (row snapshot parent : PendingDestination) (storage : ReceivingStorage)
    (resolved : destinationCurrent state incoming = .ok current)
    (present : state.destinations[current]? = some row) (inactive : row.progress = .abandoned)
    (saved : state.destinationResumptions.lookup current = some snapshot)
    (adaptation : snapshot.adaptation = none) (layout : snapshot.layout = .elements)
    (use : snapshot.use = .child parentId) (stored : state.storage[snapshot.storage]? = some storage)
    (start : snapshot.capability.start ≤ storage.bytes.size)
    (parentFound : state.destinations[parentId]? = some parent) (parentPhase : parent.progress = .suspended count current)
    (successors : DestinationSuccessorsValid state)
    (executed : renewReceivingDestination incoming state = .ok selected final) :
    destinationCurrent final current = .ok selected := by
  obtain ⟨fresh, size, edges, freshRow, freshFound, freshOpen⟩ :=
    renew_abandoned_child_successor state final incoming current parentId count selected row snapshot parent storage
      resolved present inactive saved adaptation layout use stored start parentFound parentPhase executed
  have currentInside := (destinationCurrent_bounds state incoming current resolved).2
  have beforeFresh : current < selected := by rw [fresh]; exact currentInside
  have oldTerminal : state.destinationSuccessors.lookup selected = none := by
    cases found : state.destinationSuccessors.lookup selected with
    | none => rfl
    | some next =>
      have bounds := successors selected next found
      have impossible : selected < state.destinations.size := Nat.lt_trans bounds.1 bounds.2
      rw [fresh] at impossible
      exact False.elim (Nat.lt_irrefl _ impossible)
  have currentEdge : final.destinationSuccessors.lookup current = some selected := by
    simp [edges]
  have selectedTerminal : final.destinationSuccessors.lookup selected = none := by
    have different : (selected == current) = false := beq_eq_false_iff_ne.mpr (Ne.symm (Nat.ne_of_lt beforeFresh))
    simp only [edges, List.lookup, different, oldTerminal]
  have currentFinal : current < final.destinations.size := by rw [size]; omega
  have selectedFinal : selected < final.destinations.size := by rw [size, fresh]; omega
  simp only [destinationCurrent_result, destinationCurrentSteps_succ, currentFinal, ↓reduceIte,
    currentEdge, beforeFresh]
  rw [size]
  simp only [destinationCurrentSteps_succ, selectedFinal, ↓reduceIte, selectedTerminal]

theorem renewed_child_self_carrier_lands_without_old_anchor (state final : ConstructionState)
    (incoming current parentId count selected : Nat)
    (row snapshot parent : PendingDestination) (storage : ReceivingStorage)
    (resolved : destinationCurrent state incoming = .ok current)
    (present : state.destinations[current]? = some row) (inactive : row.progress = .abandoned)
    (saved : state.destinationResumptions.lookup current = some snapshot)
    (adaptation : snapshot.adaptation = none) (layout : snapshot.layout = .elements)
    (use : snapshot.use = .child parentId) (stored : state.storage[snapshot.storage]? = some storage)
    (start : snapshot.capability.start ≤ storage.bytes.size)
    (parentFound : state.destinations[parentId]? = some parent) (parentPhase : parent.progress = .suspended count current)
    (execution : ExecutionState) (origin : OriginId)
    (successors : DestinationSuccessorsValid state)
    (executed : renewReceivingDestination incoming state = .ok selected final) :
    landCarriersInto origin [.construct current] [.completed selected] { execution with construction := final } =
      .ok () { execution with construction := final } := by
  have current' := renew_abandoned_child_resolves_to_fresh state final incoming current parentId count selected
    row snapshot parent storage resolved present inactive saved adaptation layout use stored start parentFound parentPhase successors executed
  simp [landCarriersInto, receivingDestination, liftConstruction, current', bind, pure]

#print axioms renewed_child_self_carrier_lands_without_old_anchor
#print axioms renew_abandoned_child_resolves_to_fresh
#print axioms renew_abandoned_child_successor
#print axioms renewed_child_blocks_old_anchor_commit
#print axioms renew_abandoned_child_retargets_parent

end Goose.Proofs.ConstructionAcceptedExecution
