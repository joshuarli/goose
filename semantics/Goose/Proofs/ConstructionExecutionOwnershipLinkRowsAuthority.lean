import Goose.Proofs.ConstructionExecutionOwnershipReplacementSupport
import Goose.Proofs.ConstructionExecutionProtocolReservationFrames

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

def ReplacementOwnerState (selected : DestinationId) (progress : DestinationProgress) : Prop :=
  (∃ count, progress = .exiting count selected) ∨ progress = .abandoned ∨ progress = .cancelled

theorem replacementSupported_congr_destinations (before after : ConstructionState)
    (same : after.destinations = before.destinations) (id : DestinationId)
    (supported : ReplacementSupported before id) : ReplacementSupported after id := by
  induction supported with
  | active index row present live => exact .active index row (by simpa only [same] using present) live
  | parent index parent row present use supported ih =>
      exact .parent index parent row (by simpa only [same] using present) use ih

theorem supportedReplacementAuthority_congr_destinations (before after : ConstructionState)
    (same : after.destinations = before.destinations) (valid : SupportedReplacementAuthority before) :
    SupportedReplacementAuthority after := by
  intro id parent row present use supported
  obtain ⟨owner, found, backing, phase⟩ := valid id parent row (by simpa only [same] using present) use
    (replacementSupported_congr_destinations after before same.symm id supported)
  exact ⟨owner, by simpa only [same] using found, backing, phase⟩

abbrev SupportedReplacementAuthorityRows (rows : Array PendingDestination) : Prop :=
  SupportedReplacementAuthority { ConstructionState.initial with destinations := rows }

theorem supportedReplacementAuthority_rows_frame (before after : ConstructionState)
    (frame : SupportedReplacementAuthorityRows before.destinations → SupportedReplacementAuthorityRows after.destinations)
    (valid : SupportedReplacementAuthority before) : SupportedReplacementAuthority after :=
  supportedReplacementAuthority_congr_destinations
    { ConstructionState.initial with destinations := after.destinations } after rfl
    (frame (supportedReplacementAuthority_congr_destinations before
      { ConstructionState.initial with destinations := before.destinations } rfl valid))

theorem replacementSupported_replace_back (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (useBack : ∀ parent, after.use = .replacement parent → before.use = .replacement parent)
    (activeBack : activeProgress after.progress = true → activeProgress before.progress = true)
    (index : DestinationId)
    (supported : ReplacementSupported { state with destinations := state.destinations.set! id after } index) :
    ReplacementSupported state index := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  induction supported with
  | active index row found live =>
      by_cases same : id = index
      · subst index
        have equal : after = row := by
          simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt inside,
            Option.some.injEq] using found
        subst row
        exact .active id before present (activeBack live)
      · exact .active index row (by simpa only [Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_ne same] using found) live
  | parent index parent row found use supported ih =>
      by_cases same : id = index
      · subst index
        have equal : after = row := by
          simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt inside,
            Option.some.injEq] using found
        subst row
        exact .parent id parent before present (useBack parent use) ih
      · apply ReplacementSupported.parent index parent row _ use ih
        simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same] using found

private theorem replacementOwner_replace (state : ConstructionState) (id selected index : DestinationId)
    (before after owner : PendingDestination) (present : state.destinations[id]? = some before)
    (ownerPresent : state.destinations[index]? = some owner)
    (phase : ReplacementOwnerState selected owner.progress)
    (ownerBack : ∀ target, ReplacementOwnerState target before.progress →
      after.backing = before.backing ∧ ReplacementOwnerState target after.progress) :
    ∃ current, (state.destinations.set! id after)[index]? = some current ∧
      current.backing = owner.backing ∧ ReplacementOwnerState selected current.progress := by
  by_cases same : id = index
  · subst index
    have equal := Option.some.inj (present.symm.trans ownerPresent)
    subst owner
    have inside := (Array.getElem?_eq_some_iff.mp present).1
    exact ⟨after, Array.getElem?_setIfInBounds_self_of_lt inside, ownerBack selected phase⟩
  · exact ⟨owner, by simpa only [Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne same] using ownerPresent, rfl, phase⟩

theorem supportedReplacementAuthority_replace (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (useBack : ∀ parent, after.use = .replacement parent →
      before.use = .replacement parent ∧ after.backing = before.backing)
    (activeBack : activeProgress after.progress = true → activeProgress before.progress = true)
    (ownerBack : ∀ target, ReplacementOwnerState target before.progress →
      after.backing = before.backing ∧ ReplacementOwnerState target after.progress)
    (valid : SupportedReplacementAuthority state) :
    SupportedReplacementAuthority { state with destinations := state.destinations.set! id after } := by
  intro index parent row found use supported
  have priorSupport := replacementSupported_replace_back state id before after present
    (fun target selected => (useBack target selected).1) activeBack index supported
  have prior : ∃ initial, state.destinations[index]? = some initial ∧
      initial.use = .replacement parent ∧ row.backing = initial.backing := by
    by_cases same : id = index
    · subst index
      have inside := (Array.getElem?_eq_some_iff.mp present).1
      have equal : after = row := by
        simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt inside,
          Option.some.injEq] using found
      subst row
      exact ⟨before, present, useBack parent use⟩
    · exact ⟨row, by simpa only [Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_ne same] using found, use, rfl⟩
  obtain ⟨initial, initialPresent, initialUse, rowBacking⟩ := prior
  obtain ⟨owner, ownerPresent, ownerBacking, ownerPhase⟩ := valid index parent initial initialPresent initialUse priorSupport
  obtain ⟨current, currentPresent, currentBacking, currentPhase⟩ :=
    replacementOwner_replace state id index parent before after owner present ownerPresent ownerPhase ownerBack
  exact ⟨current, currentPresent, rowBacking.trans (ownerBacking.trans currentBacking.symm), currentPhase⟩


theorem replacementSupported_push_back (state : ConstructionState) (added : PendingDestination)
    (notReplacement : ∀ parent, added.use ≠ .replacement parent) (index : DestinationId)
    (inside : index < state.destinations.size)
    (supported : ReplacementSupported { state with destinations := state.destinations.push added } index) :
    ReplacementSupported state index := by
  revert inside
  induction supported with
  | active id row present live =>
      intro inside
      exact .active id row (by simpa only [Array.getElem?_push, Nat.ne_of_lt inside, ↓reduceIte] using present) live
  | parent id parent row present use supported ih =>
      intro inside
      by_cases fresh : id = state.destinations.size
      · subst id
        have equal : added = row := by simpa only [Array.getElem?_push_size, Option.some.injEq] using present
        subst row
        exact False.elim (notReplacement parent use)
      · have oldPresent : state.destinations[id]? = some row := by
          simpa only [Array.getElem?_push, fresh, ↓reduceIte] using present
        exact .parent id parent row oldPresent use (ih (Array.getElem?_eq_some_iff.mp oldPresent).1)

theorem supportedReplacementAuthority_push (state : ConstructionState) (added : PendingDestination)
    (notReplacement : ∀ parent, added.use ≠ .replacement parent)
    (valid : SupportedReplacementAuthority state) :
    SupportedReplacementAuthority { state with destinations := state.destinations.push added } := by
  intro id parent row present use supported
  have fresh : id ≠ state.destinations.size := by
    intro same
    subst id
    have equal : added = row := by simpa only [Array.getElem?_push_size, Option.some.injEq] using present
    subst row
    exact notReplacement parent use
  have oldPresent : state.destinations[id]? = some row := by
    simpa only [Array.getElem?_push, fresh, ↓reduceIte] using present
  obtain ⟨owner, ownerPresent, backing, phase⟩ := valid id parent row oldPresent use
    (replacementSupported_push_back state added notReplacement id
      (Array.getElem?_eq_some_iff.mp oldPresent).1 supported)
  have parentInside := (Array.getElem?_eq_some_iff.mp ownerPresent).1
  exact ⟨owner, by simpa only [Array.getElem?_push, Nat.ne_of_lt parentInside, ↓reduceIte] using ownerPresent,
    backing, phase⟩


theorem supportedReplacementAuthority_replace_mutable (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (sameUse : after.use = before.use) (backing : OwnershipLinkBacking before after)
    (mutable : ¬ ReservationStableProgress before.progress) (valid : SupportedReplacementAuthority state) :
    SupportedReplacementAuthority { state with destinations := state.destinations.set! id after } := by
  apply supportedReplacementAuthority_replace state id before after present ?_ ?_ ?_ valid
  · intro parent use
    have original := sameUse.symm.trans use
    exact ⟨original, by simpa only [OwnershipLinkBacking, original] using backing⟩
  · intro _
    cases progress : before.progress <;> simp_all [ReservationStableProgress, activeProgress]
  · intro target phase
    rcases phase with ⟨count, progress⟩ | progress | progress <;>
      exact False.elim (mutable (by simp [ReservationStableProgress, progress]))

theorem supportedReplacementAuthority_replace_inactive (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (sameUse : after.use = before.use) (sameBacking : after.backing = before.backing)
    (progress : after.progress = before.progress ∨ after.progress = .abandoned ∨ after.progress = .cancelled)
    (valid : SupportedReplacementAuthority state) :
    SupportedReplacementAuthority { state with destinations := state.destinations.set! id after } := by
  apply supportedReplacementAuthority_replace state id before after present ?_ ?_ ?_ valid
  · intro parent use
    exact ⟨sameUse.symm.trans use, sameBacking⟩
  · intro live
    rcases progress with same | abandoned | cancelled
    · simpa only [same] using live
    · simp [abandoned, activeProgress] at live
    · simp [cancelled, activeProgress] at live
  · intro target phase
    refine ⟨sameBacking, ?_⟩
    rcases progress with same | abandoned | cancelled
    · simpa only [same] using phase
    · exact Or.inr (Or.inl abandoned)
    · exact Or.inr (Or.inr cancelled)

theorem replacementSupported_push_replace_back (state : ConstructionState) (id : DestinationId)
    (before after added : PendingDestination) (present : state.destinations[id]? = some before)
    (sameUse : after.use = before.use) (active : activeProgress before.progress = true)
    (addedParent : ∀ parent, added.use = .replacement parent → parent = id)
    (index : DestinationId) (inside : index < state.destinations.size)
    (supported : ReplacementSupported
      { state with destinations := (state.destinations.push added).set! id after } index) :
    ReplacementSupported state index := by
  have idInside := (Array.getElem?_eq_some_iff.mp present).1
  have pushedPresent : (state.destinations.push added)[id]? = some before := by
    simpa only [Array.getElem?_push, Nat.ne_of_lt idInside, ↓reduceIte] using present
  have afterPresent : ((state.destinations.push added).set! id after)[id]? = some after :=
    Array.getElem?_setIfInBounds_self_of_lt (by simpa using Nat.lt_succ_of_lt idInside)
  have readOld : ∀ index row, index < state.destinations.size →
      ((state.destinations.push added).set! id after)[index]? = some row →
      ∃ original, state.destinations[index]? = some original ∧
        (row = after ∧ index = id ∨ row = original) := by
    intro index row inside found
    by_cases same : id = index
    · subst index
      exact ⟨before, present, Or.inl ⟨Option.some.inj (found.symm.trans afterPresent), rfl⟩⟩
    · refine ⟨row, ?_, Or.inr rfl⟩
      simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same,
        Array.getElem?_push, Nat.ne_of_lt inside, ↓reduceIte] using found
  revert inside
  induction supported with
  | active index row found live =>
      intro inside
      obtain ⟨original, originalPresent, changed | unchanged⟩ := readOld index row inside found
      · rcases changed with ⟨_, rfl⟩
        exact .active _ before present active
      · subst row
        exact .active index original originalPresent live
  | parent index parent row found use supported ih =>
      intro inside
      by_cases fresh : index = state.destinations.size
      · subst index
        have different : id ≠ state.destinations.size := Nat.ne_of_lt idInside
        have equal : added = row := by
          simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different,
            Array.getElem?_push_size, Option.some.injEq] using found
        subst row
        have same := addedParent parent use
        subst parent
        exact .active _ before present active
      · have indexInside : index < state.destinations.size := by
          have bound : index < state.destinations.size + 1 := by
            simpa only [Array.size_set!, Array.size_push] using (Array.getElem?_eq_some_iff.mp found).1
          exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ bound) fresh
        obtain ⟨original, originalPresent, changed | unchanged⟩ := readOld index row indexInside found
        · rcases changed with ⟨rfl, rfl⟩
          exact .parent _ parent before present (sameUse.symm.trans use) (ih indexInside)
        · subst row
          exact .parent index parent original originalPresent use (ih indexInside)

theorem supportedReplacementAuthority_push_replace_mutable (state : ConstructionState) (id : DestinationId)
    (before after added : PendingDestination) (present : state.destinations[id]? = some before)
    (sameUse : after.use = before.use) (sameBacking : after.backing = before.backing)
    (mutable : ¬ ReservationStableProgress before.progress)
    (addedParent : ∀ parent, added.use = .replacement parent →
      parent = id ∧ added.backing = before.backing ∧ ∃ count, after.progress = .exiting count state.destinations.size)
    (valid : SupportedReplacementAuthority state) :
    SupportedReplacementAuthority { state with destinations := (state.destinations.push added).set! id after } := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have active : activeProgress before.progress = true := by
    cases progress : before.progress <;> simp_all [ReservationStableProgress, activeProgress]
  have idDifferent : id ≠ state.destinations.size := Nat.ne_of_lt inside
  have pushedInside : id < (state.destinations.push added).size := by simpa only [Array.size_push] using Nat.lt_succ_of_lt inside
  have pushedPresent : (state.destinations.push added)[id]? = some before := by
    simpa only [Array.getElem?_push, idDifferent, ↓reduceIte] using present
  intro index parent row found use supported
  by_cases fresh : index = state.destinations.size
  · subst index
    have equal : added = row := by
      simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne idDifferent,
        Array.getElem?_push_size, Option.some.injEq] using found
    subst row
    obtain ⟨rfl, backing, count, progress⟩ := addedParent parent use
    exact ⟨after, Array.getElem?_setIfInBounds_self_of_lt pushedInside,
      backing.trans sameBacking.symm, Or.inl ⟨count, progress⟩⟩
  · have indexInside : index < state.destinations.size := by
      have bound : index < state.destinations.size + 1 := by
        simpa only [Array.size_set!, Array.size_push] using (Array.getElem?_eq_some_iff.mp found).1
      exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ bound) fresh
    have supportBefore := replacementSupported_push_replace_back state id before after added present sameUse active
      (fun target selected => (addedParent target selected).1) index indexInside supported
    have prior : ∃ original, state.destinations[index]? = some original ∧
        original.use = .replacement parent ∧ row.backing = original.backing := by
      by_cases same : id = index
      · subst index
        have equal : after = row := by
          simpa only [Array.set!_eq_setIfInBounds,
            Array.getElem?_setIfInBounds_self_of_lt pushedInside, Option.some.injEq] using found
        subst row
        exact ⟨before, present, sameUse.symm.trans use, sameBacking⟩
      · exact ⟨row, by simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same,
          Array.getElem?_push, fresh, ↓reduceIte] using found, use, rfl⟩
    obtain ⟨original, originalPresent, originalUse, originalBacking⟩ := prior
    obtain ⟨owner, ownerPresent, backing, phase⟩ := valid index parent original originalPresent originalUse supportBefore
    have ownerInside := (Array.getElem?_eq_some_iff.mp ownerPresent).1
    have pushedOwner : (state.destinations.push added)[parent]? = some owner := by
      simpa only [Array.getElem?_push, Nat.ne_of_lt ownerInside, ↓reduceIte] using ownerPresent
    obtain ⟨current, currentPresent, currentBacking, currentPhase⟩ :=
      replacementOwner_replace { state with destinations := state.destinations.push added } id index parent
        before after owner pushedPresent pushedOwner phase (by
          intro target phase
          rcases phase with ⟨count, progress⟩ | progress | progress <;>
            exact False.elim (mutable (by simp [ReservationStableProgress, progress])))
    exact ⟨current, currentPresent, originalBacking.trans (backing.trans currentBacking.symm), currentPhase⟩

end Goose.Proofs.ConstructionExecutionOwnership
