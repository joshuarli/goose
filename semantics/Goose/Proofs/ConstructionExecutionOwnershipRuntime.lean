import Goose.Proofs.ConstructionExecutionOwnershipCleanup
import Goose.Proofs.ConstructionExecutionOwnershipTree
import Goose.Construct.Runtime

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct
open Goose.Core (DestinationId OriginId)

theorem cleanupDestination_protected_exact (state : ExecutionState) (origin : OriginId)
    (id replacement : DestinationId) (carriers : List Goose.Construct.Carrier)
    (destination : PendingDestination)
    (present : state.construction.destinations[id]? = some destination)
    (active : activeProgress destination.progress = true)
    (replacementFound : protectedReplacement? state.construction id carriers = some replacement)
    (indexed : DestinationCapabilitiesIndexed state.construction)
    (checked : ∃ rows, protectedExitDiscarded state.construction id replacement = .ok rows) :
    cleanupDestination origin id carriers state = .ok ()
      { state with construction :=
        abandonRowsState (protectedRows state.construction id replacement) state.construction } := by
  simp only [cleanupDestination, getDestination, EvalM.get, bind, present, pure,
    active, Bool.not_true, Bool.false_eq_true, ↓reduceIte, replacementFound, liftConstruction,
    abandonPreservingExit_exact state.construction id replacement indexed checked]

theorem protectDestination_ok (state final : ExecutionState) (origin : OriginId)
    (id : DestinationId) (action : EvalM α) (value : α)
    (result : action state = .ok value final) :
    protectDestination origin id action state = .ok value final := by
  simp only [protectDestination, result]

theorem protectDestination_stop (state final : ExecutionState) (origin : OriginId)
    (id : DestinationId) (action : EvalM α) (reason : Goose.Core.Stop)
    (result : action state = .stop reason final) :
    protectDestination origin id action state = .stop reason final := by
  simp only [protectDestination, result]

theorem protectDestination_escape_protected_exact (state final : ExecutionState)
    (origin : OriginId) (id replacement : DestinationId) (action : EvalM α)
    (target : ExitAddress) (carriers : List Goose.Construct.Carrier) (destination : PendingDestination)
    (result : action state = .escape target carriers final)
    (present : final.construction.destinations[id]? = some destination)
    (active : activeProgress destination.progress = true)
    (replacementFound : protectedReplacement? final.construction id carriers = some replacement)
    (indexed : DestinationCapabilitiesIndexed final.construction)
    (checked : ∃ rows, protectedExitDiscarded final.construction id replacement = .ok rows) :
    protectDestination origin id action state = .escape target carriers
      { final with construction :=
        abandonRowsState (protectedRows final.construction id replacement) final.construction } := by
  simp only [protectDestination, result,
    cleanupDestination_protected_exact final origin id replacement carriers destination
      present active replacementFound indexed checked]

theorem protectDestination_break_protected_exact (state final : ExecutionState)
    (origin : OriginId) (id replacement : DestinationId) (action : EvalM α)
    (target : Nat) (carriers : List Goose.Construct.Carrier) (destination : PendingDestination)
    (result : action state = .jump target (.breakValue carriers) final)
    (present : final.construction.destinations[id]? = some destination)
    (active : activeProgress destination.progress = true)
    (replacementFound : protectedReplacement? final.construction id carriers = some replacement)
    (indexed : DestinationCapabilitiesIndexed final.construction)
    (checked : ∃ rows, protectedExitDiscarded final.construction id replacement = .ok rows) :
    protectDestination origin id action state = .jump target (.breakValue carriers)
      { final with construction :=
        abandonRowsState (protectedRows final.construction id replacement) final.construction } := by
  simp only [protectDestination, result,
    cleanupDestination_protected_exact final origin id replacement carriers destination
      present active replacementFound indexed checked]

theorem cleanupDestination_tree_transition (state : ExecutionState) (origin : OriginId)
    (id : DestinationId) (carriers : List Goose.Construct.Carrier) (destination : PendingDestination)
    (present : state.construction.destinations[id]? = some destination)
    (active : activeProgress destination.progress = true)
    (noReplacement : protectedReplacement? state.construction id carriers = none)
    (noCarrier : carriers.any (fun carrier => match carrier with
      | .completed destination => destination == id
      | _ => false) = false) :
    cleanupDestination origin id carriers state = liftConstruction origin (abandonTree id) state := by
  simp only [cleanupDestination, getDestination, EvalM.get, bind, present, pure,
    active, Bool.not_true, Bool.false_eq_true, ↓reduceIte, noReplacement]
  split
  · rename_i hasCarrier
    have impossible : false = true := noCarrier.symm.trans hasCarrier
    contradiction
  · rfl

theorem cleanupDestination_tree_success_exact (state final : ExecutionState) (origin : OriginId)
    (id : DestinationId) (carriers : List Goose.Construct.Carrier) (destination : PendingDestination)
    (present : state.construction.destinations[id]? = some destination)
    (active : activeProgress destination.progress = true)
    (noReplacement : protectedReplacement? state.construction id carriers = none)
    (noCarrier : carriers.any (fun carrier => match carrier with
      | .completed destination => destination == id
      | _ => false) = false)
    (indexed : DestinationCapabilitiesIndexed state.construction)
    (result : cleanupDestination origin id carriers state = .ok () final) :
    final = { state with construction :=
      treeAbandonRowsState (treeRows state.construction id) state.construction } := by
  simp only [cleanupDestination, getDestination, EvalM.get, bind, present, pure,
    active, Bool.not_true, Bool.false_eq_true, ↓reduceIte, noReplacement, noCarrier,
    liftConstruction] at result
  split at result
  · rename_i hasCarrier
    have impossible : false = true := noCarrier.symm.trans hasCarrier
    contradiction
  · simp only [liftConstruction] at result
    cases cleaned : abandonTree id state.construction with
    | fault kind construction => simp only [cleaned] at result; contradiction
    | ok token construction =>
        cases token
        simp only [cleaned] at result
        cases result
        rw [abandonTree_success_exact state.construction construction id indexed cleaned]

theorem protectDestination_continue_tree_success_exact (state pending final : ExecutionState)
    (origin : OriginId) (id target : Nat) (action : EvalM α) (destination : PendingDestination)
    (result : action state = .jump target .continueLoop pending)
    (present : pending.construction.destinations[id]? = some destination)
    (active : activeProgress destination.progress = true)
    (indexed : DestinationCapabilitiesIndexed pending.construction)
    (propagated : protectDestination origin id action state = .jump target .continueLoop final) :
    final = { pending with construction := treeAbandonRowsState (treeRows pending.construction id) pending.construction } := by
  simp only [protectDestination, result] at propagated
  simp only [cleanupDestination, getDestination, EvalM.get, bind, present, pure,
    active, Bool.not_true, Bool.false_eq_true, ↓reduceIte, protectedReplacement?, List.findSome?_nil,
    List.any_nil, liftConstruction] at propagated
  cases cleaned : abandonTree id pending.construction with
  | fault kind construction => simp only [cleaned] at propagated; contradiction
  | ok token construction =>
      cases token
      simp only [cleaned] at propagated
      cases propagated
      rw [abandonTree_success_exact pending.construction construction id indexed cleaned]

theorem protectDestination_escape_tree_success_exact (state pending final : ExecutionState)
    (origin : OriginId) (id : DestinationId) (action : EvalM α) (target : ExitAddress)
    (carriers : List Goose.Construct.Carrier) (destination : PendingDestination)
    (result : action state = .escape target carriers pending)
    (present : pending.construction.destinations[id]? = some destination)
    (active : activeProgress destination.progress = true)
    (noReplacement : protectedReplacement? pending.construction id carriers = none)
    (noCarrier : carriers.any (fun carrier => match carrier with
      | .completed destination => destination == id
      | _ => false) = false)
    (indexed : DestinationCapabilitiesIndexed pending.construction)
    (propagated : protectDestination origin id action state = .escape target carriers final) :
    final = { pending with construction := treeAbandonRowsState (treeRows pending.construction id) pending.construction } := by
  simp only [protectDestination, result,
    cleanupDestination_tree_transition pending origin id carriers destination present active noReplacement noCarrier,
    liftConstruction] at propagated
  cases cleaned : abandonTree id pending.construction with
  | fault kind construction => simp only [cleaned] at propagated; contradiction
  | ok token construction =>
      cases token
      simp only [cleaned] at propagated
      cases propagated
      rw [abandonTree_success_exact pending.construction construction id indexed cleaned]

theorem protectDestination_break_tree_success_exact (state pending final : ExecutionState)
    (origin : OriginId) (id target : Nat) (action : EvalM α)
    (carriers : List Goose.Construct.Carrier) (destination : PendingDestination)
    (result : action state = .jump target (.breakValue carriers) pending)
    (present : pending.construction.destinations[id]? = some destination)
    (active : activeProgress destination.progress = true)
    (noReplacement : protectedReplacement? pending.construction id carriers = none)
    (noCarrier : carriers.any (fun carrier => match carrier with
      | .completed destination => destination == id
      | _ => false) = false)
    (indexed : DestinationCapabilitiesIndexed pending.construction)
    (propagated : protectDestination origin id action state = .jump target (.breakValue carriers) final) :
    final = { pending with construction := treeAbandonRowsState (treeRows pending.construction id) pending.construction } := by
  simp only [protectDestination, result,
    cleanupDestination_tree_transition pending origin id carriers destination present active noReplacement noCarrier,
    liftConstruction] at propagated
  cases cleaned : abandonTree id pending.construction with
  | fault kind construction => simp only [cleaned] at propagated; contradiction
  | ok token construction =>
      cases token
      simp only [cleaned] at propagated
      cases propagated
      rw [abandonTree_success_exact pending.construction construction id indexed cleaned]

end Goose.Proofs.ConstructionExecutionOwnership
