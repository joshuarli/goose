import Goose.Proofs.ConstructionExitChildRenewal

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

private theorem destinationCurrentSteps_redirect (before after : ConstructionState)
    (current selected : Nat)
    (size : after.destinations.size = before.destinations.size + 1)
    (edges : after.destinationSuccessors = (current, selected) :: before.destinationSuccessors)
    (currentInside : current < before.destinations.size)
    (selectedInside : selected < after.destinations.size) (forward : current < selected)
    (terminal : after.destinationSuccessors.lookup selected = none)
    (fuel incoming : Nat) (resolved : destinationCurrentSteps fuel before incoming = .ok current) :
    destinationCurrentSteps (fuel + 1) after incoming = .ok selected := by
  induction fuel generalizing incoming with
  | zero => simp only [destinationCurrentSteps_zero] at resolved; cases resolved
  | succ fuel ih =>
    by_cases same : incoming = current
    · subst incoming
      have currentAfter : current < after.destinations.size := by omega
      have currentEdge : after.destinationSuccessors.lookup current = some selected := by simp [edges]
      simp only [destinationCurrentSteps_succ, currentAfter, ↓reduceIte, currentEdge, forward,
        selectedInside, terminal]
    · rw [destinationCurrentSteps_succ] at resolved
      by_cases inside : incoming < before.destinations.size
      · have afterInside : incoming < after.destinations.size := by omega
        simp only [inside, ↓reduceIte] at resolved
        have sameEdge : after.destinationSuccessors.lookup incoming = before.destinationSuccessors.lookup incoming := by
          have mismatch : (incoming == current) = false := beq_eq_false_iff_ne.mpr same
          simp only [edges, List.lookup, mismatch]
        rw [destinationCurrentSteps_succ]
        simp only [afterInside, ↓reduceIte, sameEdge]
        cases edge : before.destinationSuccessors.lookup incoming with
        | none =>
          simp only [edge, Except.ok.injEq] at resolved
          exact False.elim (same resolved)
        | some next =>
          simp only [edge] at resolved ⊢
          by_cases ahead : incoming < next
          · simp only [ahead, ↓reduceIte] at resolved ⊢
            exact ih next resolved
          · simp [ahead] at resolved
      · simp [inside] at resolved

theorem destinationCurrent_redirect (before after : ConstructionState) (incoming current selected : Nat)
    (size : after.destinations.size = before.destinations.size + 1)
    (edges : after.destinationSuccessors = (current, selected) :: before.destinationSuccessors)
    (selectedInside : selected < after.destinations.size) (forward : current < selected)
    (terminal : after.destinationSuccessors.lookup selected = none)
    (resolved : destinationCurrent before incoming = .ok current) :
    destinationCurrent after incoming = .ok selected := by
  have currentInside := (destinationCurrent_bounds before incoming current resolved).2
  have result := destinationCurrentSteps_redirect before after current selected size edges currentInside selectedInside forward terminal
    (before.destinations.size + 1) incoming resolved
  simpa only [destinationCurrent_result, size] using result

theorem renewed_child_alias_lands_without_old_anchor (state final : ConstructionState)
    (incoming current parentId count selected : Nat)
    (row snapshot parent : PendingDestination) (storage : ReceivingStorage)
    (resolved : destinationCurrent state incoming = .ok current)
    (present : state.destinations[current]? = some row) (inactive : row.progress = .abandoned)
    (saved : state.destinationResumptions.lookup current = some snapshot)
    (adaptation : snapshot.adaptation = none) (layout : snapshot.layout = .elements)
    (use : snapshot.use = .child parentId) (stored : state.storage[snapshot.storage]? = some storage)
    (start : snapshot.capability.start ≤ storage.bytes.size)
    (parentFound : state.destinations[parentId]? = some parent) (parentPhase : parent.progress = .suspended count current)
    (execution : ExecutionState) (origin : OriginId) (successors : DestinationSuccessorsValid state)
    (executed : renewReceivingDestination incoming state = .ok selected final) :
    destinationCurrent final incoming = .ok selected ∧
      landCarriersInto origin [.construct incoming] [.completed selected] { execution with construction := final } =
        .ok () { execution with construction := final } := by
  obtain ⟨fresh, size, edges, freshRow, freshFound, freshOpen⟩ :=
    renew_abandoned_child_successor state final incoming current parentId count selected row snapshot parent storage
      resolved present inactive saved adaptation layout use stored start parentFound parentPhase executed
  have currentInside := (destinationCurrent_bounds state incoming current resolved).2
  have forward : current < selected := by rw [fresh]; exact currentInside
  have oldTerminal : state.destinationSuccessors.lookup selected = none := by
    cases found : state.destinationSuccessors.lookup selected with
    | none => rfl
    | some next =>
      have bounds := successors selected next found
      have impossible : selected < state.destinations.size := Nat.lt_trans bounds.1 bounds.2
      rw [fresh] at impossible
      exact False.elim (Nat.lt_irrefl _ impossible)
  have terminal : final.destinationSuccessors.lookup selected = none := by
    have different : (selected == current) = false := beq_eq_false_iff_ne.mpr (Ne.symm (Nat.ne_of_lt forward))
    simp only [edges, List.lookup, different, oldTerminal]
  have inside : selected < final.destinations.size := by rw [size, fresh]; omega
  have result := destinationCurrent_redirect state final incoming current selected size edges inside forward terminal resolved
  refine ⟨result, ?_⟩
  simp [landCarriersInto, receivingDestination, liftConstruction, result, bind, pure]

#print axioms renewed_child_alias_lands_without_old_anchor
#print axioms destinationCurrent_redirect

end Goose.Proofs.ConstructionAcceptedExecution
