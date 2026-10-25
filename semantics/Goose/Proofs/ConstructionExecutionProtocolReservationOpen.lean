import Goose.Proofs.ConstructionExecutionProtocolReservations

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

private abbrev needsPrefix (layout : ReceivingLayout) (request : ConstructionRequest) : Bool :=
  (fun {left right : Bool} (_ : left = right) => left) (hasPrefix_result layout request)

private theorem snapshotPhase_after_open (state : ConstructionState) (current : DestinationId)
    (snapshot replacement : PendingDestination) (count : Nat) (storage : Array ReceivingStorage)
    (present : state.destinations[current]? = some snapshot)
    (correct : snapshot.capability.id = current) (valid : DestinationLifecycleInvariant state) :
    ReservedSnapshotPhase { state with
      storage := storage
      destinations := (state.destinations.push replacement).set! current
        { snapshot with progress := .exiting count state.destinations.size }
      events := state.events ++ [.begin state.destinations.size] } snapshot := by
  have inside := (Array.getElem?_eq_some_iff.mp present).choose
  have afterInside : current < (state.destinations.push replacement).size := by
    simpa only [Array.size_push] using Nat.lt_succ_of_lt inside
  intro row found
  simp only [correct, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt afterInside,
    Option.some.injEq] at found
  subst row
  intro phase accepted
  have previous := valid.1 current
  rw [present] at previous
  obtain ⟨prior, runPrior, matched⟩ := previous
  have trace : runDestinationTrace current .unseen (state.events ++ [.begin state.destinations.size]) =
      runDestinationTrace current .unseen state.events := by
    rw [runDestinationTrace_append]
    simp [runDestinationTrace, destinationObservations, observeDestination,
      Nat.ne_of_lt inside, (Nat.ne_of_lt inside).symm, runDestinationObservations]
  simp only [correct, trace] at accepted
  have same : prior = phase := Option.some.inj (runPrior.symm.trans accepted)
  subst phase
  exact matched

theorem openExitReplacement_snapshot (state : ConstructionState) (current selected : DestinationId)
    (snapshot : PendingDestination) (after : ConstructionState)
    (present : state.destinations[current]? = some snapshot)
    (opened : openExitReplacement current state = .ok selected after)
    (valid : DestinationLifecycleInvariant state) :
    selected = state.destinations.size ∧ selected < after.destinations.size ∧
      SavedDestinationProgress snapshot.progress ∧ ReservedSnapshotPhase after snapshot := by
  have correct := valid.2.1 current snapshot present
  have inside := (Array.getElem?_eq_some_iff.mp present).choose
  have insideAfter : current < state.destinations.size + 1 := Nat.lt_succ_of_lt inside
  simp only [openExitReplacement, writableDestination_result, present, bind] at opened
  cases allowed : destinationCanWrite state current with
  | false => simp only [allowed] at opened; contradiction
  | true =>
      simp only [allowed] at opened
      cases progress : snapshot.progress <;> try simp only [progress] at opened <;> try contradiction
      all_goals
        try simp only [pure, lookupStorage_result, bind] at opened
        cases stored : state.storage[snapshot.storage]? with
        | none => simp only [stored] at opened; contradiction
        | some storage =>
            have storageInside := (Array.getElem?_eq_some_iff.mp stored).choose
            simp only [stored, ConstructionM.get, ConstructionM.set, bind, replaceDestination_result,
              Array.size_push, insideAfter, ↓reduceIte] at opened
            cases prefixed : needsPrefix snapshot.layout snapshot.capability.request
            all_goals
              simp only [needsPrefix] at prefixed
              simp only [prefixed, Bool.false_eq_true, ↓reduceIte, replaceStorage_result, storageInside,
                ConstructionM.get, ConstructionM.set, bind, pure, emit_result] at opened
              cases opened
              refine ⟨rfl, by simp, by simp only [progress, SavedDestinationProgress], ?_⟩
              apply snapshotPhase_after_open state current snapshot _ _ _ present correct valid

end Goose.Proofs.ConstructionExecutionProtocol
