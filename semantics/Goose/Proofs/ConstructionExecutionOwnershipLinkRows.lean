import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsAuthority
import Goose.Proofs.ConstructionExecutionProtocolReservationFrames

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

def OwnershipChildSourceExtension (before after : ConstructionState) : Prop :=
  ∀ (id parent : DestinationId) (row : PendingDestination),
    before.destinations[id]? = some row → row.use = .child parent →
    ∃ current, after.destinations[id]? = some current ∧ current.use = .child parent ∧
      current.backing.receiverStorage = row.backing.receiverStorage

theorem ownershipChildSourceExtension_of_sourceExtension (before after : ConstructionState)
    (extension : OwnershipSourceExtension before after) : OwnershipChildSourceExtension before after := by
  intro id parent row present use
  obtain ⟨current, found, sameUse, backing⟩ := extension id row present
  exact ⟨current, found, sameUse.trans use, by simpa only [OwnershipLinkBacking, use] using backing⟩

theorem ownershipChildSourceExtension_refl (state : ConstructionState) :
    OwnershipChildSourceExtension state state := by
  intro id parent row present use
  exact ⟨row, present, use, rfl⟩

theorem ownershipChildSourceExtension_trans (before middle after : ConstructionState)
    (first : OwnershipChildSourceExtension before middle)
    (second : OwnershipChildSourceExtension middle after) : OwnershipChildSourceExtension before after := by
  intro id parent row present use
  obtain ⟨interim, found, interimUse, interimBacking⟩ := first id parent row present use
  obtain ⟨final, finalPresent, finalUse, finalBacking⟩ := second id parent interim found interimUse
  exact ⟨final, finalPresent, finalUse, finalBacking.trans interimBacking⟩

theorem destinationForwardLink_childSourceExtension (before after : ConstructionState)
    (extension : OwnershipChildSourceExtension before after) (id : DestinationId) (row : PendingDestination)
    (progress : SavedDestinationProgress row.progress) (valid : DestinationForwardLink before id row) :
    DestinationForwardLink after id row := by
  cases step : row.progress <;> simp only [DestinationForwardLink, step] at valid ⊢
  all_goals try trivial
  all_goals try { simp only [SavedDestinationProgress, step] at progress }
  obtain ⟨selected, present, use, backing⟩ := valid
  obtain ⟨current, found, sameUse, sameBacking⟩ := extension _ id selected present use
  exact ⟨current, found, sameUse, sameBacking.trans backing⟩

def OwnershipExitingRowsFrame (before after : ConstructionState) : Prop :=
  ∀ (id : DestinationId) (initial final : PendingDestination),
    before.destinations[id]? = some initial → after.destinations[id]? = some final →
    ∀ count selected, initial.progress = .exiting count selected →
      ∀ finalCount finalSelected, final.progress = .exiting finalCount finalSelected →
        final = initial

theorem ownershipExitingRowsFrame_refl (state : ConstructionState) :
    OwnershipExitingRowsFrame state state := by
  intro id initial final initialPresent finalPresent
  exact fun _ _ _ _ _ _ => Option.some.inj (finalPresent.symm.trans initialPresent)

theorem ownershipExitingRowsFrame_trans (before middle after : ConstructionState)
    (firstMetadata : ReservationMetadataFrame before middle)
    (first : OwnershipExitingRowsFrame before middle)
    (secondMetadata : ReservationMetadataFrame middle after)
    (second : OwnershipExitingRowsFrame middle after) : OwnershipExitingRowsFrame before after := by
  intro id initial final initialPresent finalPresent count selected initialExiting finalCount finalSelected finalExiting
  have inside := (Array.getElem?_eq_some_iff.mp initialPresent).1
  have middleInside := Nat.lt_of_lt_of_le inside firstMetadata.destinations
  let interim := middle.destinations[id]
  have interimPresent : middle.destinations[id]? = some interim := Array.getElem?_eq_getElem middleInside
  obtain ⟨interimStable, _⟩ := firstMetadata.rows.preserves id initial interim initialPresent interimPresent
    (by simp [ReservationStableProgress, initialExiting])
  obtain ⟨_, interimExiting⟩ :=
    secondMetadata.rows.preserves id interim final interimPresent finalPresent interimStable
  obtain ⟨midCount, midSelected, midExiting, _⟩ := interimExiting finalCount finalSelected finalExiting
  exact (second id interim final interimPresent finalPresent midCount midSelected midExiting
    finalCount finalSelected finalExiting).trans
      (first id initial interim initialPresent interimPresent count selected initialExiting
        midCount midSelected midExiting)

theorem ownershipExitingRowsFrame_same_rows (before after : ConstructionState)
    (rows : after.destinations = before.destinations) : OwnershipExitingRowsFrame before after := by
  intro id initial final initialPresent finalPresent
  rw [rows] at finalPresent
  exact fun _ _ _ _ _ _ => Option.some.inj (finalPresent.symm.trans initialPresent)

theorem ownershipExitingRowsFrame_replace (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (unchanged : ∀ count selected, before.progress = .exiting count selected →
      ∀ finalCount finalSelected, after.progress = .exiting finalCount finalSelected → after = before) :
    OwnershipExitingRowsFrame state { state with destinations := state.destinations.set! id after } := by
  intro index initial final initialPresent finalPresent count selected initialExiting finalCount finalSelected finalExiting
  by_cases same : id = index
  · subst index
    have inside := (Array.getElem?_eq_some_iff.mp present).1
    have sameInitial := Option.some.inj (initialPresent.symm.trans present)
    have sameFinal : after = final := by
      simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt inside,
        Option.some.injEq] using finalPresent
    subst initial
    subst final
    exact unchanged count selected initialExiting finalCount finalSelected finalExiting
  · have original : state.destinations[index]? = some final := by
      simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same] using finalPresent
    exact Option.some.inj (original.symm.trans initialPresent)

theorem ownershipExitingRowsFrame_push (state : ConstructionState) (row : PendingDestination) :
    OwnershipExitingRowsFrame state { state with destinations := state.destinations.push row } := by
  intro id initial final initialPresent finalPresent
  have inside := (Array.getElem?_eq_some_iff.mp initialPresent).1
  have original : state.destinations[id]? = some final := by
    simpa only [Array.getElem?_push, Nat.ne_of_lt inside, ↓reduceIte] using finalPresent
  exact fun _ _ _ _ _ _ => Option.some.inj (original.symm.trans initialPresent)

theorem freshReservationSnapshotAuthority_frame (before after : ConstructionState)
    (valid : ReservationLifecycleInvariant before) (frame : ReservationMetadataFrame before after)
    (rows : OwnershipExitingRowsFrame before after)
    (authority : FreshReservationSnapshotAuthority before) : FreshReservationSnapshotAuthority after := by
  intro token incoming selected snapshot current ticket different currentPresent count replacement exiting
  rw [frame.tickets] at ticket
  have active := valid.2.active token .fresh incoming selected snapshot ticket
  have originalInside := active.1.allocated
  let original := before.destinations[snapshot.capability.id]
  have originalPresent : before.destinations[snapshot.capability.id]? = some original :=
    Array.getElem?_eq_getElem originalInside
  have phase := (active.2.2.2 (Ne.symm different)).2 original originalPresent
  have stable : ReservationStableProgress original.progress := by
    cases progress : original.progress <;>
      simp_all only [ReservedSnapshotPhase, ReservationStableProgress]
  obtain ⟨_, previous⟩ := frame.rows.preserves snapshot.capability.id original current originalPresent currentPresent stable
  obtain ⟨oldCount, oldSelected, oldExiting, _⟩ := previous count replacement exiting
  have same := rows snapshot.capability.id original current originalPresent currentPresent
    oldCount oldSelected oldExiting count replacement exiting
  subst current
  exact authority token incoming selected snapshot original ticket different originalPresent
    count replacement exiting

def OwnershipLinkRowsFrame (before after : ConstructionState) : Prop :=
  OwnershipChildSourceExtension before after ∧ OwnershipExitingRowsFrame before after ∧
    (SupportedReplacementAuthorityRows before.destinations → SupportedReplacementAuthorityRows after.destinations)

theorem OwnershipLinkRowsFrame.children {before after : ConstructionState}
    (frame : OwnershipLinkRowsFrame before after) : OwnershipChildSourceExtension before after := frame.1

theorem OwnershipLinkRowsFrame.exiting {before after : ConstructionState}
    (frame : OwnershipLinkRowsFrame before after) : OwnershipExitingRowsFrame before after := frame.2.1

theorem OwnershipLinkRowsFrame.authority {before after : ConstructionState}
    (frame : OwnershipLinkRowsFrame before after) (valid : SupportedReplacementAuthority before) :
    SupportedReplacementAuthority after := supportedReplacementAuthority_rows_frame before after frame.2.2 valid

theorem OwnershipLinkRowsFrame.refl (state : ConstructionState) : OwnershipLinkRowsFrame state state :=
  ⟨ownershipChildSourceExtension_refl state, ownershipExitingRowsFrame_refl state, id⟩

theorem OwnershipLinkRowsFrame.trans {before middle after : ConstructionState}
    (firstMetadata : ReservationMetadataFrame before middle)
    (secondMetadata : ReservationMetadataFrame middle after)
    (first : OwnershipLinkRowsFrame before middle) (second : OwnershipLinkRowsFrame middle after) :
    OwnershipLinkRowsFrame before after :=
  ⟨ownershipChildSourceExtension_trans before middle after first.children second.children,
    ownershipExitingRowsFrame_trans before middle after firstMetadata first.exiting secondMetadata second.exiting,
    fun valid => second.2.2 (first.2.2 valid)⟩

theorem ownershipLinkRowsFrame_same_rows (before after : ConstructionState)
    (same : after.destinations = before.destinations) : OwnershipLinkRowsFrame before after := by
  refine ⟨?_, ownershipExitingRowsFrame_same_rows before after same, ?_⟩
  · intro id parent row present use
    exact ⟨row, by simpa only [same] using present, use, rfl⟩
  · intro valid
    simpa only [same] using valid

theorem ownershipLinkRowsFrame_replace (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (child : ∀ parent, before.use = .child parent → after.use = .child parent ∧
      after.backing.receiverStorage = before.backing.receiverStorage)
    (exiting : ∀ count selected, before.progress = .exiting count selected →
      ∀ finalCount finalSelected, after.progress = .exiting finalCount finalSelected → after = before)
    (useBack : ∀ parent, after.use = .replacement parent →
      before.use = .replacement parent ∧ after.backing = before.backing)
    (activeBack : activeProgress after.progress = true → activeProgress before.progress = true)
    (ownerBack : ∀ target, ReplacementOwnerState target before.progress →
      after.backing = before.backing ∧ ReplacementOwnerState target after.progress) :
    OwnershipLinkRowsFrame state { state with destinations := state.destinations.set! id after } := by
  refine ⟨?_, ownershipExitingRowsFrame_replace state id before after present exiting, ?_⟩
  · intro index parent row found use
    by_cases same : id = index
    · subst index
      have equal := Option.some.inj (present.symm.trans found)
      subst row
      have inside := (Array.getElem?_eq_some_iff.mp present).1
      exact ⟨after, Array.getElem?_setIfInBounds_self_of_lt inside, child parent use⟩
    · exact ⟨row, by simpa only [Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_ne same] using found, use, rfl⟩
  · exact supportedReplacementAuthority_replace
      { ConstructionState.initial with destinations := state.destinations } id before after present
      useBack activeBack ownerBack

theorem ownershipLinkRowsFrame_push (state : ConstructionState) (row : PendingDestination)
    (notReplacement : ∀ parent, row.use ≠ .replacement parent) :
    OwnershipLinkRowsFrame state { state with destinations := state.destinations.push row } := by
  exact ⟨ownershipChildSourceExtension_of_sourceExtension state _ (ownershipSourceExtension_push state row),
    ownershipExitingRowsFrame_push state row,
    supportedReplacementAuthority_push { ConstructionState.initial with destinations := state.destinations }
      row notReplacement⟩

theorem ownershipLinkRowsFrame_replace_mutable (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (sameUse : after.use = before.use) (backing : OwnershipLinkBacking before after)
    (mutable : ¬ ReservationStableProgress before.progress) :
    OwnershipLinkRowsFrame state { state with destinations := state.destinations.set! id after } := by
  refine ownershipLinkRowsFrame_replace state id before after present ?_ ?_ ?_ ?_ ?_
  · intro parent use
    exact ⟨sameUse.trans use, by simpa only [OwnershipLinkBacking, use] using backing⟩
  · intro count selected exiting
    exact False.elim (mutable (by simp [ReservationStableProgress, exiting]))

  · intro parent use
    have original := sameUse.symm.trans use
    exact ⟨original, by simpa only [OwnershipLinkBacking, original] using backing⟩
  · intro _
    cases progress : before.progress <;> simp_all [ReservationStableProgress, activeProgress]
  · intro target phase
    rcases phase with ⟨count, progress⟩ | progress | progress <;>
      exact False.elim (mutable (by simp [ReservationStableProgress, progress]))

theorem ownershipLinkRowsFrame_replace_terminal (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (sameUse : after.use = before.use) (backing : OwnershipLinkBacking before after)
    (terminal : ∀ count selected, after.progress ≠ .exiting count selected)
    (sameBacking : after.backing = before.backing)
    (phase : after.progress = before.progress ∨ after.progress = .abandoned ∨ after.progress = .cancelled) :
    OwnershipLinkRowsFrame state { state with destinations := state.destinations.set! id after } := by
  refine ownershipLinkRowsFrame_replace state id before after present ?_ ?_ ?_ ?_ ?_
  · intro parent use
    exact ⟨sameUse.trans use, by simpa only [OwnershipLinkBacking, use] using backing⟩
  · intro _ _ _ count selected exiting
    exact False.elim (terminal count selected exiting)

  · intro parent use
    exact ⟨sameUse.symm.trans use, sameBacking⟩
  · intro live
    rcases phase with same | abandoned | cancelled
    · simpa only [same] using live
    · simp [abandoned, activeProgress] at live
    · simp [cancelled, activeProgress] at live
  · intro target beforePhase
    refine ⟨sameBacking, ?_⟩
    rcases phase with same | abandoned | cancelled
    · simpa only [same] using beforePhase
    · exact Or.inr (Or.inl abandoned)
    · exact Or.inr (Or.inr cancelled)

theorem ownershipLinkRowsFrame_push_replace_mutable (state : ConstructionState) (id : DestinationId)
    (before after added : PendingDestination) (present : state.destinations[id]? = some before)
    (sameUse : after.use = before.use) (backing : OwnershipLinkBacking before after)
    (mutable : ¬ ReservationStableProgress before.progress)
    (sameBacking : after.backing = before.backing)
    (addedParent : ∀ parent, added.use = .replacement parent →
      parent = id ∧ added.backing = before.backing ∧ ∃ count, after.progress = .exiting count state.destinations.size) :
    OwnershipLinkRowsFrame state { state with destinations := (state.destinations.push added).set! id after } := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have pushed : (state.destinations.push added)[id]? = some before := by
    simpa only [Array.getElem?_push, Nat.ne_of_lt inside, ↓reduceIte] using present
  have updated := ownershipLinkRowsFrame_replace_mutable
    { state with destinations := state.destinations.push added } id before after pushed sameUse backing mutable
  refine ⟨?_, ?_, ?_⟩
  · exact ownershipChildSourceExtension_trans state _ _
      (ownershipChildSourceExtension_of_sourceExtension state _ (ownershipSourceExtension_push state added)) updated.children
  · intro index initial final initialPresent finalPresent count selected initialExiting finalCount finalSelected finalExiting
    have indexInside := (Array.getElem?_eq_some_iff.mp initialPresent).1
    have unchanged : (state.destinations.push added)[index]? = some initial := by
      simpa only [Array.getElem?_push, Nat.ne_of_lt indexInside, ↓reduceIte] using initialPresent
    exact updated.exiting index initial final unchanged finalPresent count selected initialExiting
      finalCount finalSelected finalExiting
  · exact supportedReplacementAuthority_push_replace_mutable
      { ConstructionState.initial with destinations := state.destinations } id before after added present
      sameUse sameBacking mutable addedParent

theorem ownershipLinkRowsFrame_two_mutable (state : ConstructionState) (first second : DestinationId)
    (beforeFirst beforeSecond afterFirst afterSecond : PendingDestination)
    (firstPresent : state.destinations[first]? = some beforeFirst)
    (secondPresent : state.destinations[second]? = some beforeSecond) (different : first ≠ second)
    (firstUse : afterFirst.use = beforeFirst.use) (secondUse : afterSecond.use = beforeSecond.use)
    (firstBacking : OwnershipLinkBacking beforeFirst afterFirst)
    (secondBacking : OwnershipLinkBacking beforeSecond afterSecond)
    (firstMutable : ¬ ReservationStableProgress beforeFirst.progress)
    (secondMutable : ¬ ReservationStableProgress beforeSecond.progress) :
    OwnershipLinkRowsFrame state { state with
      destinations := (state.destinations.set! first afterFirst).set! second afterSecond } := by
  let middle := { state with destinations := state.destinations.set! first afterFirst }
  have secondPresent' : middle.destinations[second]? = some beforeSecond := by
    simpa only [middle, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different] using secondPresent
  have firstFrame := ownershipLinkRowsFrame_replace_mutable state first beforeFirst afterFirst firstPresent
    firstUse firstBacking firstMutable
  have secondFrame := ownershipLinkRowsFrame_replace_mutable middle second beforeSecond afterSecond secondPresent'
    secondUse secondBacking secondMutable
  refine ⟨?_, ?_, ?_⟩
  · exact ownershipChildSourceExtension_trans state middle _ firstFrame.children secondFrame.children
  · intro id initial final initialPresent finalPresent count selected initialExiting finalCount finalSelected finalExiting
    have notFirst : first ≠ id := by
      intro same
      subst id
      have equal := Option.some.inj (firstPresent.symm.trans initialPresent)
      subst initial
      exact firstMutable (by simp [ReservationStableProgress, initialExiting])
    have notSecond : second ≠ id := by
      intro same
      subst id
      have equal := Option.some.inj (secondPresent.symm.trans initialPresent)
      subst initial
      exact secondMutable (by simp [ReservationStableProgress, initialExiting])
    have original : state.destinations[id]? = some final := by
      simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne notSecond,
        Array.getElem?_setIfInBounds_ne notFirst] using finalPresent
    exact Option.some.inj (original.symm.trans initialPresent)

  · intro valid
    exact secondFrame.2.2 (firstFrame.2.2 valid)

theorem constructionOwnershipLinks_rows_frame (before after : ConstructionState)
    (reservation : ReservationLifecycleInvariant before) (valid : ConstructionOwnershipLinks before)
    (metadata : ReservationMetadataFrame before after) (rows : OwnershipLinkRowsFrame before after)
    (bounded : DestinationLifecycleInvariant after) (forward : DestinationForwardLinks after) :
    ConstructionOwnershipLinks after := by
  rcases valid with ⟨_, _, saved, fresh, authority, direct, resumed⟩
  refine ⟨bounded, forward, ⟨?_, ?_⟩, ?_,
    freshReservationSnapshotAuthority_frame before after reservation metadata rows.exiting authority, ?_, ?_⟩
  · intro token incoming selected snapshot present
    rw [metadata.tickets] at present
    obtain ⟨count, opened | built | suspended⟩ := fresh token incoming selected snapshot present
    · exact destinationForwardLink_childSourceExtension before after rows.children _ _
        (by simp [SavedDestinationProgress, opened]) (saved.1 token incoming selected snapshot present)
    · exact destinationForwardLink_childSourceExtension before after rows.children _ _
        (by simp [SavedDestinationProgress, built]) (saved.1 token incoming selected snapshot present)
    · obtain ⟨child, suspended⟩ := suspended
      exact destinationForwardLink_childSourceExtension before after rows.children _ _
        (by simp [SavedDestinationProgress, suspended]) (saved.1 token incoming selected snapshot present)
  · intro id snapshot present
    rw [metadata.resumptions] at present
    simp only [DestinationForwardLink, resumed id snapshot present]
  · intro token incoming selected snapshot present
    rw [metadata.tickets] at present
    exact fresh token incoming selected snapshot present
  · intro token incoming selected snapshot present same
    rw [metadata.tickets] at present
    exact direct token incoming selected snapshot present same
  · intro id snapshot present
    rw [metadata.resumptions] at present
    exact resumed id snapshot present

theorem reserveStorage_ownership_rows (bytes : ByteArray) (count : Nat) (state : ConstructionState) :
    OwnershipLinkRowsFrame state (reserveStorage bytes count state).finalState := by
  apply ownershipLinkRowsFrame_same_rows
  rfl

theorem appendStdout_ownership_rows (bytes : ByteArray) (state : ConstructionState) :
    OwnershipLinkRowsFrame state (appendStdout bytes state).finalState := by
  apply ownershipLinkRowsFrame_same_rows
  rfl

end Goose.Proofs.ConstructionExecutionOwnership
