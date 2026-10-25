import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsCleanup

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

theorem destinationForwardLinks_adopt_replacement (state : ConstructionState) (id old : DestinationId)
    (before after superseded : PendingDestination) (present : state.destinations[id]? = some before)
    (oldPresent : state.destinations[old]? = some superseded) (replacement : before.use = .replacement old)
    (oldLeaf : OwnershipLeafProgress superseded.progress) (newLeaf : OwnershipLeafProgress after.progress)
    (valid : DestinationForwardLinks state) :
    DestinationForwardLinks { state with destinations := state.destinations.set! id after } := by
  intro index row found
  by_cases same : id = index
  · subst index
    have inside := (Array.getElem?_eq_some_iff.mp present).1
    have equal : after = row := by
      simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt inside,
        Option.some.injEq] using found
    subst row
    cases progress : after.progress <;> simp_all [DestinationForwardLink, OwnershipLeafProgress]
  · have original : state.destinations[index]? = some row := by
      simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same] using found
    have link := valid index row original
    cases progress : row.progress <;> simp only [DestinationForwardLink, progress] at link ⊢
    all_goals try trivial
    all_goals
      obtain ⟨selected, selectedPresent, use, backing⟩ := link
      rename_i count target
      by_cases changed : id = target
      · subst target
        have equal := Option.some.inj (present.symm.trans selectedPresent)
        subst selected
        first
        | solve | simp [replacement] at use
        | solve
          | have owner : old = index := DestinationUse.replacement.inj (replacement.symm.trans use)
            subst index
            have sameOld := Option.some.inj (oldPresent.symm.trans original)
            subst row
            simp [progress, OwnershipLeafProgress] at oldLeaf
      · exact ⟨selected, by simpa only [Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_ne changed] using selectedPresent, use, backing⟩

theorem ownershipForwardRowsFrame_adopt_replacement (state : ConstructionState) (id old count : DestinationId)
    (before after superseded : PendingDestination) (present : state.destinations[id]? = some before)
    (oldPresent : state.destinations[old]? = some superseded) (replacement : before.use = .replacement old)
    (progress : before.progress = .built count)
    (oldLeaf : OwnershipLeafProgress superseded.progress) (newLeaf : OwnershipLeafProgress after.progress)
    (notReplacement : ∀ parent, after.use ≠ .replacement parent) :
    OwnershipForwardRowsFrame state { state with destinations := state.destinations.set! id after } := by
  constructor
  · refine ownershipLinkRowsFrame_replace state id before after present ?_ ?_ ?_ ?_ ?_
    · intro parent child
      simp [replacement] at child
    · intro _ _ exiting
      simp [progress] at exiting
    · intro parent use
      exact False.elim (notReplacement parent use)
    · intro _
      simp [activeProgress, progress]
    · intro target phase
      rcases phase with ⟨prior, exiting⟩ | abandoned | cancelled <;> simp [progress] at *
  · exact destinationForwardLinks_adopt_replacement state id old before after superseded present oldPresent
      replacement oldLeaf newLeaf

theorem ownershipForwardRowsFrame_suspend_existing (state : ConstructionState) (parentId child count : DestinationId)
    (parent selected : PendingDestination) (parentPresent : state.destinations[parentId]? = some parent)
    (selectedPresent : state.destinations[child]? = some selected) (selectedUse : selected.use = .child parentId)
    (backing : selected.backing.receiverStorage = parent.storage)
    (mutable : ¬ ReservationStableProgress parent.progress) :
    OwnershipForwardRowsFrame state { state with
      destinations := state.destinations.set! parentId { parent with progress := .suspended count child } } := by
  constructor
  · exact ownershipLinkRowsFrame_replace_mutable state parentId parent _ parentPresent rfl
      (by cases use : parent.use <;> simp [OwnershipLinkBacking, use]) mutable
  · intro valid
    refine destinationForwardLinks_replace_sources state parentId parent _ parentPresent ?_ ?_ valid ?_
    · rfl
    · cases use : parent.use <;> simp [OwnershipLinkBacking, use]
    · exact ⟨selected, selectedPresent, selectedUse, backing⟩

theorem ownershipForwardRowsFrame_land_parent (state : ConstructionState) (parentId old child count : DestinationId)
    (parent superseded selected : PendingDestination) (parentPresent : state.destinations[parentId]? = some parent)
    (oldPresent : state.destinations[old]? = some superseded)
    (selectedPresent : state.destinations[child]? = some selected)
    (progress : parent.progress = .suspended count old)
    (sameUse : selected.use = superseded.use) (sameBacking : selected.backing = superseded.backing) :
    OwnershipForwardRowsFrame state { state with
      destinations := state.destinations.set! parentId { parent with progress := .suspended count child } } := by
  constructor
  · exact ownershipLinkRowsFrame_replace_mutable state parentId parent _ parentPresent rfl
      (by cases use : parent.use <;> simp [OwnershipLinkBacking, use])
      (by simp [ReservationStableProgress, progress])
  · intro valid
    have link := valid parentId parent parentPresent
    simp only [DestinationForwardLink, progress] at link
    obtain ⟨current, currentPresent, use, backing⟩ := link
    have equal := Option.some.inj (oldPresent.symm.trans currentPresent)
    subst current
    exact (ownershipForwardRowsFrame_suspend_existing state parentId child count parent selected parentPresent
      selectedPresent (sameUse.trans use) (by simpa only [sameBacking] using backing)
      (by simp [ReservationStableProgress, progress])).2 valid

end Goose.Proofs.ConstructionExecutionOwnership
