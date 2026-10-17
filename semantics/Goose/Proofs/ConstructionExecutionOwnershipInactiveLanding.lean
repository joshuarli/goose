import Goose.Proofs.ConstructionExecutionOwnershipLinkReservationsLandingTables
import Goose.Proofs.ConstructionExecutionOwnershipResumptionBacking

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

private theorem cleanup_inactive_support (state : ConstructionState) (root final : DestinationId)
    (valid : DestinationLifecycleInvariant state) :
    InactiveBackingExtension state (abandonRowsState (protectedRows state root final) state) ∧
      ReplacementSupportExtension state (abandonRowsState (protectedRows state root final) state) := by
  let rows := protectedRows state root final
  let after := abandonRowsState rows state
  have current := protectedRows_current state root final valid.2.1
  have unique := (protectedRows_indexed state root final valid.2.1).2
  constructor
  · intro id row present inactive
    have inside : id < after.destinations.size := by
      rw [(abandonRowsState_frame rows state).2.2.1]
      exact (Array.getElem?_eq_some_iff.mp present).1
    let finalRow := after.destinations[id]
    have finalPresent : after.destinations[id]? = some finalRow := Array.getElem?_eq_getElem inside
    obtain ⟨original, originalPresent, metadata, phase⟩ := abandonRowsState_metadata_lookup rows state current unique id finalRow finalPresent
    have equal := Option.some.inj (originalPresent.symm.trans present)
    subst original
    have sameBacking := congrArg PendingDestination.backing metadata
    refine ⟨finalRow, finalPresent, ?_, sameBacking⟩
    rcases phase with same | abandoned
    · simpa only [same] using inactive
    · simp only [abandoned, activeProgress]
  · intro id _ supported
    induction supported with
    | active index row present live => exact .active index row (abandonRowsState_active_unchanged rows state index row present live) live
    | parent index parent row present use supported ih =>
        obtain ⟨original, originalPresent, originalUse⟩ := abandonRowsState_use_lookup rows state current unique index row present
        exact .parent index parent original originalPresent (originalUse.trans use) (ih (Array.getElem?_eq_some_iff.mp originalPresent).1)

private theorem rewire_inactive (state : ConstructionState) (root final : DestinationId)
    (landed anchor finalRow : PendingDestination) (update : Option (DestinationId × PendingDestination))
    (valid : DestinationLifecycleInvariant state) (earlier : root < final)
    (anchorPresent : state.destinations[root]? = some anchor)
    (finalPresent : state.destinations[final]? = some finalRow)
    (built : ∃ count, finalRow.progress = .built count)
    (choice : OwnershipLandingParentChoice state root final anchor update) :
    InactiveBackingExtension state (protectedCleanupRewireState state root final landed update) := by
  intro id row present inactive
  have different : id ≠ final := by
    intro same
    subst id
    cases Option.some.inj (present.symm.trans finalPresent)
    obtain ⟨count, progress⟩ := built
    simp only [progress, activeProgress, Bool.true_eq_false] at inactive
  obtain ⟨current, currentPresent⟩ := protectedCleanupRewire_existing state root final landed update id row present
  obtain ⟨original, originalPresent, metadata, phase⟩ := protectedCleanupRewire_metadata state root final landed anchor update
    valid earlier anchorPresent choice id current different currentPresent
  have equal := Option.some.inj (originalPresent.symm.trans present)
  subst original
  have sameBacking := congrArg PendingDestination.backing metadata
  refine ⟨current, currentPresent, ?_, sameBacking⟩
  rcases phase with same | abandoned | ⟨count, suspended, updated⟩ | ⟨count, exiting, updated⟩
  · simpa only [same] using inactive
  · simp only [abandoned, activeProgress]
  · simp only [suspended, activeProgress, Bool.true_eq_false] at inactive
  · simp only [exiting, activeProgress, Bool.true_eq_false] at inactive

private theorem inactive_support_congr (before original after : ConstructionState)
    (same : after.destinations = original.destinations)
    (valid : InactiveBackingExtension before original ∧ ReplacementSupportExtension before original) :
    InactiveBackingExtension before after ∧ ReplacementSupportExtension before after := by
  constructor
  · simpa only [InactiveBackingExtension, same] using valid.1
  · intro id inside supported
    exact valid.2 id inside (replacementSupported_congr_destinations after original same.symm id supported)

private theorem inactive_support_refl (state : ConstructionState) :
    InactiveBackingExtension state state ∧ ReplacementSupportExtension state state :=
  ⟨inactiveBackingExtension_refl state, replacementSupportExtension_refl state⟩

theorem completedStep_inactive_support (state : ConstructionState) (id root count : Nat)
    (replacement anchor : PendingDestination) (update : Option (DestinationId × PendingDestination))
    (valid : DestinationLifecycleInvariant state) (earlier : root < id)
    (present : state.destinations[id]? = some replacement) (progress : replacement.progress = .built count)
    (anchorPresent : state.destinations[root]? = some anchor)
    (path : OwnershipReplacementPath state.destinations root id)
    (choice : OwnershipLandingParentChoice state root id anchor update) :
    InactiveBackingExtension state (completedStep id root count replacement anchor update state).finalState ∧
      ReplacementSupportExtension state (completedStep id root count replacement anchor update state).finalState := by
  have tables := completedStep_ownership_tables state id root count replacement anchor update valid earlier present anchorPresent choice
  rcases tables with same | same | same
  · exact inactive_support_congr state state _ same (inactive_support_refl state)
  · exact inactive_support_congr state _ _ same (cleanup_inactive_support state root id valid)
  · apply inactive_support_congr state _ _ same
    refine ⟨rewire_inactive state root id _ anchor replacement update valid earlier anchorPresent present ⟨count, progress⟩ choice, ?_⟩
    intro index _ supported
    exact protectedCleanupRewire_support_back state root id (ownershipLandedRow count replacement anchor) anchor replacement update valid earlier
      (ownershipLandingParentChoice_parent state root id anchor update valid.2.2.2 anchorPresent choice)
      (ownershipLandingParentChoice_active state root id anchor update valid.2.2.2 anchorPresent choice)
      present (by simp only [progress, activeProgress]) anchorPresent rfl path index supported

private abbrev landingLookupDestination (id : DestinationId) : ConstructionM PendingDestination := fun state =>
  (fun {left right : ConstructionResult PendingDestination} (_ : left = right) => left) (lookupDestination_result id state)

theorem landExitReplacement_inactive_support (id : DestinationId) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state) :
    InactiveBackingExtension state (landExitReplacement id state).finalState ∧
      ReplacementSupportExtension state (landExitReplacement id state).finalState := by
  have unchanged := inactive_support_refl state
  simp only [landExitReplacement, landingLookupDestination, lookupDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact unchanged
  | some replacement =>
      simp only [present]
      cases use : replacement.use <;> try simp only [use] <;> try exact unchanged
      case replacement root =>
        cases progress : replacement.progress <;> try simp only [progress] <;> try exact unchanged
        case built count =>
          simp only [pure, bind, landingLookupDestination, lookupDestination_result]
          have earlier : root < id := by simpa only [use] using valid.2.2.2 id replacement present
          cases anchorPresent : state.destinations[root]? with
          | none => exact unchanged
          | some anchor =>
              simp only [anchorPresent, bind]
              have path : OwnershipReplacementPath state.destinations root id := .step id root root replacement present use (.refl root)
              have finish (update : Option (DestinationId × PendingDestination))
                  (choice : OwnershipLandingParentChoice state root id anchor update) :=
                completedStep_inactive_support state id root count replacement anchor update valid earlier present progress anchorPresent path choice
              have finishUse : InactiveBackingExtension state (((do
                  let parentUpdate ← match anchor.use with
                    | .receiver => pure none
                    | .child parentId => do
                        let parent ← landingLookupDestination parentId
                        match parent.progress with
                        | .suspended parentCount expected =>
                            if expected != root then ConstructionM.fail .ownership
                            pure (some (parentId, {parent with progress := .suspended parentCount id}))
                        | _ => ConstructionM.fail .protocol
                    | .replacement _ => ConstructionM.fail .protocol
                  completedStep id root count replacement anchor parentUpdate) : ConstructionM Unit) state).finalState ∧
                  ReplacementSupportExtension state (((do
                  let parentUpdate ← match anchor.use with
                    | .receiver => pure none
                    | .child parentId => do
                        let parent ← landingLookupDestination parentId
                        match parent.progress with
                        | .suspended parentCount expected =>
                            if expected != root then ConstructionM.fail .ownership
                            pure (some (parentId, {parent with progress := .suspended parentCount id}))
                        | _ => ConstructionM.fail .protocol
                    | .replacement _ => ConstructionM.fail .protocol
                  completedStep id root count replacement anchor parentUpdate) : ConstructionM Unit) state).finalState := by
                cases anchorUse : anchor.use with
                | receiver => exact finish none (by simp only [OwnershipLandingParentChoice, anchorUse])
                | replacement parent => exact unchanged
                | child parentId =>
                    simp only [landingLookupDestination, lookupDestination_result, bind]
                    cases parentPresent : state.destinations[parentId]? with
                    | none => exact unchanged
                    | some parent =>
                        simp only [parentPresent, bind]
                        cases parentProgress : parent.progress <;> try simp only [parentProgress] <;> try exact unchanged
                        case suspended parentCount expected =>
                          by_cases expectedEq : expected = root
                          · subst expected
                            simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, bind]
                            exact finish _ (by
                              simp only [OwnershipLandingParentChoice, anchorUse]
                              exact ⟨parent, parentCount, parentPresent, parentProgress, rfl⟩)
                          · simp only [bne_iff_ne, if_pos expectedEq, ConstructionM.fail, bind, ConstructionResult.finalState]
                            exact unchanged
              cases anchorProgress : anchor.progress <;> try simp only [anchorProgress] <;> try exact unchanged
              all_goals
                split
                · exact unchanged
                · have expected := finishUse
                  simp only [landingLookupDestination, lookupDestination_result, completedStep, bind, pure,
                    ConstructionM.fail] at expected ⊢
                  exact expected

end Goose.Proofs.ConstructionExecutionOwnership
