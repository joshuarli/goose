import Goose.Proofs.ExitExecutionLandingAnchor

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionExecutionProtocol

inductive LandingParentReady (state : ConstructionState) (anchorId : Nat)
    (anchor : PendingDestination) : Prop
  | receiver (use : anchor.use = .receiver) : LandingParentReady state anchorId anchor
  | child (parentId count : Nat) (parent : PendingDestination)
      (use : anchor.use = .child parentId) (present : state.destinations[parentId]? = some parent)
      (progress : parent.progress = .suspended count anchorId) : LandingParentReady state anchorId anchor
  | replacement (parentId count : Nat) (parent : PendingDestination)
      (use : anchor.use = .replacement parentId) (present : state.destinations[parentId]? = some parent)
      (progress : parent.progress = .exiting count anchorId) : LandingParentReady state anchorId anchor

def committedExitState (state : ConstructionState) (id anchorId count : Nat)
    (replacement anchor : PendingDestination) (storage : ReceivingStorage)
    (parentUpdate : Option (DestinationId × PendingDestination)) (chain : List DestinationId) : ConstructionState :=
  let landed := completedLandingState state id anchorId count replacement anchor storage parentUpdate
  { landed with destinationSuccessors := chain.map (fun previous => (previous, id)) ++ landed.destinationSuccessors }

private theorem commit_completed_suffix (state : ConstructionState) (id anchorId count : Nat)
    (replacement anchor : PendingDestination) (storage : ReceivingStorage)
    (parentUpdate : Option (DestinationId × PendingDestination)) (chain : List DestinationId)
    (indexed : DestinationCapabilitiesIndexed state)
    (present : state.destinations[id]? = some replacement)
    (stored : state.storage[replacement.storage]? = some storage)
    (ordered : anchor.capability.start ≤ replacement.capability.start)
    (inside : replacement.capability.start ≤ storage.bytes.size)
    (bound : ∀ parentId parent, parentUpdate = some (parentId, parent) → parentId < state.destinations.size) :
    ((do
      completedStep id anchorId count replacement anchor parentUpdate
      let after ← ConstructionM.get
      ConstructionM.set { after with destinationSuccessors := chain.map (fun previous => (previous, id)) ++ after.destinationSuccessors }) state) =
        .ok () (committedExitState state id anchorId count replacement anchor storage parentUpdate chain) := by
  simp only [bind]
  rw [completedStep_success state id anchorId count replacement anchor storage parentUpdate indexed present stored ordered inside bound]
  rfl

private theorem committedExitState_parent (state : ConstructionState) (id anchorId count : Nat)
    (replacement anchor : PendingDestination) (storage : ReceivingStorage)
    (parentId : DestinationId) (parent : PendingDestination) (chain : List DestinationId)
    (bound : parentId < state.destinations.size) :
    (committedExitState state id anchorId count replacement anchor storage (some (parentId, parent)) chain).destinations[parentId]? = some parent := by
  have size := (Goose.Proofs.ConstructionExecutionOwnership.abandonRowsState_frame
    (Goose.Proofs.ConstructionExecutionOwnership.protectedRows state anchorId id) state).2.2.1
  have cleanBound : parentId < (Goose.Proofs.ConstructionExecutionOwnership.abandonRowsState
      (Goose.Proofs.ConstructionExecutionOwnership.protectedRows state anchorId id) state).destinations.size := by rw [size]; exact bound
  simp only [committedExitState, completedLandingState]
  split <;> simp only [Array.set!]
  all_goals apply Array.getElem?_setIfInBounds_self_of_lt
  all_goals simpa only [Array.size_setIfInBounds] using cleanBound

theorem commitExitReplacement_of_anchor (state : ConstructionState) (id count : Nat)
    (replacement : PendingDestination) (storage : ReceivingStorage) (receiving : Option DestinationId)
    (anchorId : Nat) (anchor : PendingDestination) (chain : List DestinationId)
    (lifecycle : DestinationLifecycleInvariant state)
    (present : state.destinations[id]? = some replacement) (built : replacement.progress = .built count)
    (stored : state.storage[replacement.storage]? = some storage)
    (selected : exitLandingAnchor (state.destinations.size + 1) id replacement.storage receiving state =
      .ok (anchorId, anchor, chain) state)
    (ready : LandingParentReady state anchorId anchor)
    (ordered : anchor.capability.start ≤ replacement.capability.start)
    (inside : replacement.capability.start ≤ storage.bytes.size) :
    ∃ parentUpdate,
      commitExitReplacement receiving id state =
        .ok () (committedExitState state id anchorId count replacement anchor storage parentUpdate chain) ∧
      (∀ parentId parent, parentUpdate = some (parentId, parent) → parentId < state.destinations.size) ∧
      (∀ parentId parent, parentUpdate = some (parentId, parent) → parentId ≠ id) ∧
      (∀ parentId parent, parentUpdate = some (parentId, parent) →
        anchor.use = .child parentId ∨ anchor.use = .replacement parentId) ∧
      LandingParentReady (committedExitState state id anchorId count replacement anchor storage parentUpdate chain)
        id (landedReplacementRow replacement anchor count) := by
  obtain ⟨_, anchorEarlier, anchorPresent⟩ := exitLandingAnchor_success _ _ _ _ state state anchorId anchor chain selected
  have finish := commit_completed_suffix state id anchorId count replacement anchor storage
  cases ready with
  | receiver use =>
    have bound : ∀ parentId parent, (none : Option (DestinationId × PendingDestination)) = some (parentId, parent) →
        parentId < state.destinations.size := by intro _ _ impossible; cases impossible
    refine ⟨none, ?_, bound, ?_, ?_, .receiver use⟩
    · have suffix := finish none chain lifecycle.2.1 present stored ordered inside bound
      simpa only [commitExitReplacement, lookupDestination_result, present, built, ConstructionM.get,
        selected, use, bind, pure, completedStep] using suffix
    · intro _ _ impossible
      cases impossible
    · intro _ _ impossible
      cases impossible
  | child parentId parentCount parent use parentPresent progress =>
    let update := some (parentId, { parent with progress := .suspended parentCount id })
    have parentEarlier : parentId < anchorId := by simpa only [use] using lifecycle.2.2.2 anchorId anchor anchorPresent
    have bound : ∀ actualId actual, update = some (actualId, actual) → actualId < state.destinations.size := by
      intro actualId actual same
      have ids : parentId = actualId := congrArg Prod.fst (Option.some.inj same)
      rw [← ids]
      exact (Array.getElem?_eq_some_iff.mp parentPresent).1
    have different : ∀ actualId actual, update = some (actualId, actual) → actualId ≠ id := by
      intro actualId actual same
      have ids : parentId = actualId := congrArg Prod.fst (Option.some.inj same)
      rw [← ids]
      exact Nat.ne_of_lt (Nat.lt_trans parentEarlier anchorEarlier)
    refine ⟨update, ?_, bound, different, ?_, ?_⟩
    · have suffix := finish update chain lifecycle.2.1 present stored ordered inside bound
      simpa only [commitExitReplacement, lookupDestination_result, present, built, ConstructionM.get,
        selected, use, parentPresent, progress, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        bind, pure, completedStep, update] using suffix
    · intro actualId actual same
      have ids : parentId = actualId := congrArg Prod.fst (Option.some.inj same)
      exact Or.inl (use.trans (congrArg DestinationUse.child ids))
    · apply LandingParentReady.child parentId parentCount { parent with progress := .suspended parentCount id }
      · exact use
      · exact committedExitState_parent state id anchorId count replacement anchor storage parentId _ chain
          (Array.getElem?_eq_some_iff.mp parentPresent).1
      · rfl
  | replacement parentId parentCount parent use parentPresent progress =>
    let update := some (parentId, { parent with progress := .exiting parentCount id })
    have parentEarlier : parentId < anchorId := by simpa only [use] using lifecycle.2.2.2 anchorId anchor anchorPresent
    have bound : ∀ actualId actual, update = some (actualId, actual) → actualId < state.destinations.size := by
      intro actualId actual same
      have ids : parentId = actualId := congrArg Prod.fst (Option.some.inj same)
      rw [← ids]
      exact (Array.getElem?_eq_some_iff.mp parentPresent).1
    have different : ∀ actualId actual, update = some (actualId, actual) → actualId ≠ id := by
      intro actualId actual same
      have ids : parentId = actualId := congrArg Prod.fst (Option.some.inj same)
      rw [← ids]
      exact Nat.ne_of_lt (Nat.lt_trans parentEarlier anchorEarlier)
    refine ⟨update, ?_, bound, different, ?_, ?_⟩
    · have suffix := finish update chain lifecycle.2.1 present stored ordered inside bound
      simpa only [commitExitReplacement, lookupDestination_result, present, built, ConstructionM.get,
        selected, use, parentPresent, progress, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        bind, pure, completedStep, update] using suffix
    · intro actualId actual same
      have ids : parentId = actualId := congrArg Prod.fst (Option.some.inj same)
      exact Or.inr (use.trans (congrArg DestinationUse.replacement ids))
    · apply LandingParentReady.replacement parentId parentCount { parent with progress := .exiting parentCount id }
      · exact use
      · exact committedExitState_parent state id anchorId count replacement anchor storage parentId _ chain
          (Array.getElem?_eq_some_iff.mp parentPresent).1
      · rfl

#print axioms commitExitReplacement_of_anchor

end Goose.Proofs.ExitExecution
