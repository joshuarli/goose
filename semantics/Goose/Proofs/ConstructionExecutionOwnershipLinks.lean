import Goose.Construct.DestinationTrace

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

def DestinationForwardLink (state : ConstructionState) (id : DestinationId)
    (row : PendingDestination) : Prop :=
  match row.progress with
  | .suspended _ child => ∃ selected, state.destinations[child]? = some selected ∧
      selected.use = .child id ∧ selected.backing.receiverStorage = row.storage
  | .exiting _ replacement => ∃ selected, state.destinations[replacement]? = some selected ∧
      selected.use = .replacement id ∧ selected.backing = row.backing
  | _ => True

def DestinationForwardLinks (state : ConstructionState) : Prop :=
  ∀ id row, state.destinations[id]? = some row → DestinationForwardLink state id row

def SavedDestinationForwardLinks (state : ConstructionState) : Prop :=
  (∀ (token : ExitReservationId) (incoming selected : DestinationId) (snapshot : PendingDestination),
    state.exitReservations[token]? = some (.active .fresh incoming selected snapshot) →
    DestinationForwardLink state snapshot.capability.id snapshot) ∧
  (∀ (id : DestinationId) (snapshot : PendingDestination), state.destinationResumptions.lookup id = some snapshot →
    DestinationForwardLink state snapshot.capability.id snapshot)

def FreshReservationSnapshotProgress (state : ConstructionState) : Prop :=
  ∀ (token : ExitReservationId) (incoming selected : DestinationId) (snapshot : PendingDestination),
    state.exitReservations[token]? = some (.active .fresh incoming selected snapshot) →
    ∃ count, snapshot.progress = .open count ∨ snapshot.progress = .built count ∨
      ∃ child, snapshot.progress = .suspended count child

def FreshReservationSnapshotAuthority (state : ConstructionState) : Prop :=
  ∀ (token : ExitReservationId) (incoming selected : DestinationId) (snapshot current : PendingDestination),
    state.exitReservations[token]? = some (.active .fresh incoming selected snapshot) →
    selected ≠ snapshot.capability.id →
    state.destinations[snapshot.capability.id]? = some current →
    ∀ count replacement, current.progress = .exiting count replacement →
      { current with progress := snapshot.progress } = snapshot

def FreshDirectReservationStart (state : ConstructionState) : Prop :=
  ∀ (token : ExitReservationId) (incoming selected : DestinationId) (snapshot : PendingDestination),
    state.exitReservations[token]? = some (.active .fresh incoming selected snapshot) →
    selected = snapshot.capability.id → snapshot.progress = .open 0

def ResumptionSnapshotStart (state : ConstructionState) : Prop :=
  ∀ (id : DestinationId) (snapshot : PendingDestination),
    state.destinationResumptions.lookup id = some snapshot → snapshot.progress = .open 0

def ConstructionOwnershipLinks (state : ConstructionState) : Prop :=
  DestinationLifecycleInvariant state ∧ DestinationForwardLinks state ∧
    SavedDestinationForwardLinks state ∧ FreshReservationSnapshotProgress state ∧
    FreshReservationSnapshotAuthority state ∧ FreshDirectReservationStart state ∧ ResumptionSnapshotStart state

def OwnershipLinkBacking (before after : PendingDestination) : Prop :=
  match before.use with
  | .receiver => True
  | .child _ => after.backing.receiverStorage = before.backing.receiverStorage
  | .replacement _ => after.backing = before.backing

def OwnershipSourceExtension (before after : ConstructionState) : Prop :=
  ∀ (id : DestinationId) (row : PendingDestination), before.destinations[id]? = some row → ∃ current : PendingDestination,
    after.destinations[id]? = some current ∧ current.use = row.use ∧ OwnershipLinkBacking row current

theorem destinationForwardLink_sourceExtension (before after : ConstructionState)
    (extension : OwnershipSourceExtension before after) (id : DestinationId) (row : PendingDestination)
    (valid : DestinationForwardLink before id row) : DestinationForwardLink after id row := by
  cases progress : row.progress <;> simp only [DestinationForwardLink, progress] at valid ⊢
  all_goals
    obtain ⟨selected, present, use, backing⟩ := valid
    obtain ⟨current, found, sameUse, sameBacking⟩ := extension _ selected present
    simp only [OwnershipLinkBacking, use] at sameBacking
    exact ⟨current, found, sameUse.trans use, sameBacking.trans backing⟩

theorem ownershipSourceExtension_push (state : ConstructionState) (row : PendingDestination) :
    OwnershipSourceExtension state { state with destinations := state.destinations.push row } := by
  intro id before present
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  exact ⟨before, by simpa [Array.getElem?_push, Nat.ne_of_lt inside] using present, rfl,
    by cases use : before.use <;> simp [OwnershipLinkBacking, use]⟩

theorem ownershipSourceExtension_replace (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (sameUse : after.use = before.use) (frame : OwnershipLinkBacking before after) :
    OwnershipSourceExtension state { state with destinations := state.destinations.set! id after } := by
  intro index row found
  by_cases same : id = index
  · subst index
    have equal : before = row := Option.some.inj (present.symm.trans found)
    subst row
    have inside := (Array.getElem?_eq_some_iff.mp present).1
    exact ⟨after, Array.getElem?_setIfInBounds_self_of_lt inside, sameUse,
      frame⟩
  · exact ⟨row, by simpa [Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne same] using found, rfl,
        by cases use : row.use <;> simp [OwnershipLinkBacking, use]⟩

theorem savedDestinationForwardLinks_sourceExtension (before after : ConstructionState)
    (extension : OwnershipSourceExtension before after)
    (tickets : after.exitReservations = before.exitReservations)
    (resumptions : after.destinationResumptions = before.destinationResumptions)
    (valid : SavedDestinationForwardLinks before) : SavedDestinationForwardLinks after := by
  constructor
  · intro token incoming selected snapshot present
    rw [tickets] at present
    exact destinationForwardLink_sourceExtension before after extension _ _
      (valid.1 token incoming selected snapshot present)
  · intro id snapshot present
    rw [resumptions] at present
    exact destinationForwardLink_sourceExtension before after extension _ _ (valid.2 id snapshot present)

theorem ownershipSourceExtension_trans (before middle after : ConstructionState)
    (first : OwnershipSourceExtension before middle) (second : OwnershipSourceExtension middle after) :
    OwnershipSourceExtension before after := by
  intro id row present
  obtain ⟨mid, found, sameUse, sameBacking⟩ := first id row present
  obtain ⟨last, final, lastUse, lastBacking⟩ := second id mid found
  refine ⟨last, final, lastUse.trans sameUse, ?_⟩
  cases use : row.use <;> simp only [OwnershipLinkBacking, use, sameUse] at sameBacking lastBacking ⊢
  all_goals exact lastBacking.trans sameBacking

theorem destinationForwardLink_congr (before after : ConstructionState)
    (same : before.destinations.map (fun row => (row.use, row.backing)) =
      after.destinations.map (fun row => (row.use, row.backing)))
    (id : DestinationId) (row : PendingDestination) :
    DestinationForwardLink before id row ↔ DestinationForwardLink after id row := by
  have lookup (selected : Nat) := congrArg (fun rows => rows[selected]?) same
  simp only [Array.getElem?_map] at lookup
  cases progress : row.progress <;> simp only [DestinationForwardLink, progress]
  all_goals
    rename_i count target
    constructor <;> rintro ⟨selected, present, use, backing⟩
    · have matching := lookup target
      simp only [present, Option.map_some] at matching
      cases other : after.destinations[target]? with
      | none => simp [other] at matching
      | some value =>
          simp only [other, Option.map_some, Option.some.injEq, Prod.mk.injEq] at matching
          exact ⟨value, rfl, matching.1 ▸ use, matching.2 ▸ backing⟩
    · have matching := lookup target
      simp only [present, Option.map_some] at matching
      cases other : before.destinations[target]? with
      | none => simp [other] at matching
      | some value =>
          simp only [other, Option.map_some, Option.some.injEq, Prod.mk.injEq] at matching
          exact ⟨value, rfl, matching.1 ▸ use, matching.2 ▸ backing⟩

theorem destinationForwardLinks_push_open (state : ConstructionState) (row : PendingDestination)
    (count : Nat) (opened : row.progress = .open count) (valid : DestinationForwardLinks state) :
    DestinationForwardLinks { state with destinations := state.destinations.push row } := by
  intro id current present
  by_cases same : id = state.destinations.size
  · subst id
    have equal : row = current := by simpa using present
    subst current
    simp [DestinationForwardLink, opened]
  · have old : state.destinations[id]? = some current := by
      simpa [Array.getElem?_push, same] using present
    exact destinationForwardLink_sourceExtension state _ (ownershipSourceExtension_push state row)
      id current (valid id current old)

theorem destinationForwardLinks_replace_sources (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (sameUse : after.use = before.use) (frame : OwnershipLinkBacking before after)
    (valid : DestinationForwardLinks state) (link : DestinationForwardLink state id after) :
    DestinationForwardLinks { state with destinations := state.destinations.set! id after } := by
  let next := { state with destinations := state.destinations.set! id after }
  have extension := ownershipSourceExtension_replace state id before after present sameUse frame
  intro index row found
  apply destinationForwardLink_sourceExtension state next extension index row
  by_cases same : id = index
  · subst index
    have inside := (Array.getElem?_eq_some_iff.mp present).1
    have equal : after = row := by
      simpa [Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_self_of_lt inside] using found
    simpa [← equal] using link
  · have old : state.destinations[index]? = some row := by
      simpa [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same] using found
    exact valid index row old

theorem destinationForwardLinks_replace (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (sameUse : after.use = before.use) (sameBacking : after.backing = before.backing)
    (valid : DestinationForwardLinks state) (link : DestinationForwardLink state id after) :
    DestinationForwardLinks { state with destinations := state.destinations.set! id after } := by
  exact destinationForwardLinks_replace_sources state id before after present sameUse
    (by cases use : before.use <;> simp [OwnershipLinkBacking, use, sameBacking]) valid link

theorem destinationForwardLinks_suspend_new_child (state : ConstructionState)
    (parentId count childCount : Nat) (parent child : PendingDestination)
    (present : state.destinations[parentId]? = some parent)
    (opened : child.progress = .open childCount) (owned : child.use = .child parentId)
    (backing : child.backing.receiverStorage = parent.storage) (valid : DestinationForwardLinks state) :
    DestinationForwardLinks { state with destinations :=
      (state.destinations.push child).set! parentId { parent with progress := .suspended count state.destinations.size } } := by
  let pushed := { state with destinations := state.destinations.push child }
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have current : pushed.destinations[parentId]? = some parent := by
    simpa [pushed, Array.getElem?_push, Nat.ne_of_lt inside] using present
  apply destinationForwardLinks_replace pushed parentId parent
    { parent with progress := .suspended count state.destinations.size } current rfl rfl
    (destinationForwardLinks_push_open state child childCount opened valid)
  simp [DestinationForwardLink, pushed, owned, backing, PendingDestination.storage]

theorem destinationForwardLinks_exit_new_replacement (state : ConstructionState)
    (parentId count childCount : Nat) (parent child : PendingDestination)
    (present : state.destinations[parentId]? = some parent)
    (opened : child.progress = .open childCount) (owned : child.use = .replacement parentId)
    (backing : child.backing = parent.backing) (valid : DestinationForwardLinks state) :
    DestinationForwardLinks { state with destinations :=
      (state.destinations.push child).set! parentId { parent with progress := .exiting count state.destinations.size } } := by
  let pushed := { state with destinations := state.destinations.push child }
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have current : pushed.destinations[parentId]? = some parent := by
    simpa [pushed, Array.getElem?_push, Nat.ne_of_lt inside] using present
  apply destinationForwardLinks_replace pushed parentId parent
    { parent with progress := .exiting count state.destinations.size } current rfl rfl
    (destinationForwardLinks_push_open state child childCount opened valid)
  simp [DestinationForwardLink, pushed, owned, backing, PendingDestination.storage]

theorem initial_constructionOwnershipLinks : ConstructionOwnershipLinks .initial := by
  refine ⟨initial_destination_lifecycle_invariant, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals simp [DestinationForwardLinks, FreshReservationSnapshotProgress,
    FreshReservationSnapshotAuthority, FreshDirectReservationStart, ResumptionSnapshotStart, ConstructionState.initial]

theorem suspended_child_exact (state : ConstructionState) (valid : ConstructionOwnershipLinks state)
    (id count child : Nat) (row : PendingDestination)
    (present : state.destinations[id]? = some row) (suspended : row.progress = .suspended count child) :
    ∃ selected, state.destinations[child]? = some selected ∧
      selected.use = .child id ∧ selected.backing.receiverStorage = row.storage ∧ id < child := by
  have link := valid.2.1 id row present
  simp only [DestinationForwardLink, suspended] at link
  obtain ⟨selected, selectedPresent, use, backing⟩ := link
  exact ⟨selected, selectedPresent, use, backing, by
    simpa [use] using valid.1.2.2.2 child selected selectedPresent⟩

theorem exiting_replacement_exact (state : ConstructionState) (valid : ConstructionOwnershipLinks state)
    (id count replacement : Nat) (row : PendingDestination)
    (present : state.destinations[id]? = some row) (exiting : row.progress = .exiting count replacement) :
    ∃ selected, state.destinations[replacement]? = some selected ∧
      selected.use = .replacement id ∧ selected.backing = row.backing ∧ id < replacement := by
  have link := valid.2.1 id row present
  simp only [DestinationForwardLink, exiting] at link
  obtain ⟨selected, selectedPresent, use, backing⟩ := link
  exact ⟨selected, selectedPresent, use, backing, by
    simpa [use] using valid.1.2.2.2 replacement selected selectedPresent⟩

theorem restoreFreshSnapshot_forwardLinks (state : ConstructionState)
    (valid : ConstructionOwnershipLinks state) (token : ExitReservationId)
    (incoming selected count replacement : Nat) (snapshot current : PendingDestination)
    (ticket : state.exitReservations[token]? = some (.active .fresh incoming selected snapshot))
    (different : selected ≠ snapshot.capability.id)
    (present : state.destinations[snapshot.capability.id]? = some current)
    (exiting : current.progress = .exiting count replacement) :
    DestinationForwardLinks { state with
      destinations := state.destinations.set! snapshot.capability.id snapshot } := by
  have authority := valid.2.2.2.2.1 token incoming selected snapshot current ticket different
    present count replacement exiting
  have sameUse : snapshot.use = current.use := by
    simpa using (congrArg PendingDestination.use authority).symm
  have sameBacking : snapshot.backing = current.backing := by
    simpa using (congrArg PendingDestination.backing authority).symm
  exact destinationForwardLinks_replace state snapshot.capability.id current snapshot present
    sameUse sameBacking valid.2.1 (valid.2.2.1.1 token incoming selected snapshot ticket)

end Goose.Proofs.ConstructionExecutionOwnership
