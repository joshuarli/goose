import Goose.Proofs.ConstructionExecutionOwnershipLinkKernel
import Goose.Proofs.ConstructionExecutionOwnershipResumptionBacking
import Goose.Proofs.ConstructionExecutionOwnershipInactiveLanding
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

namespace InactiveProof

private abbrev SupportRows (before after : Array PendingDestination) : Prop :=
  ReplacementSupportExtension {ConstructionState.initial with destinations := before}
    {ConstructionState.initial with destinations := after}

private theorem support_rows (before after : ConstructionState)
    (frame : ReplacementSupportExtension before after) : SupportRows before.destinations after.destinations := by
  intro id inside supported
  exact replacementSupported_congr_destinations before {ConstructionState.initial with destinations := before.destinations} rfl id
    (frame id inside (replacementSupported_congr_destinations {ConstructionState.initial with destinations := after.destinations} after rfl id supported))

private theorem support_actual (before after : ConstructionState)
    (frame : SupportRows before.destinations after.destinations) : ReplacementSupportExtension before after := by
  intro id inside supported
  exact replacementSupported_congr_destinations {ConstructionState.initial with destinations := before.destinations} before rfl id
    (frame id inside (replacementSupported_congr_destinations after {ConstructionState.initial with destinations := after.destinations} rfl id supported))

private theorem support_rows_trans (before middle after : ConstructionState)
    (size : before.destinations.size ≤ middle.destinations.size)
    (first : SupportRows before.destinations middle.destinations)
    (second : SupportRows middle.destinations after.destinations) : SupportRows before.destinations after.destinations :=
  replacementSupportExtension_trans {ConstructionState.initial with destinations := before.destinations}
    {ConstructionState.initial with destinations := middle.destinations}
    {ConstructionState.initial with destinations := after.destinations} size first second

private def RowsFrame (before after : ConstructionState) : Prop :=
  OwnershipLinkRowsFrame before after ∧ InactiveBackingExtension before after ∧ SupportRows before.destinations after.destinations

private def ForwardFrame (before after : ConstructionState) : Prop :=
  RowsFrame before after ∧ (DestinationForwardLinks before → DestinationForwardLinks after)

private theorem inactive_same_rows (before after : ConstructionState)
    (same : after.destinations = before.destinations) : InactiveBackingExtension before after := by
  intro id row present inactive
  exact ⟨row, by simpa only [same] using present, inactive, rfl⟩

private theorem inactive_replace_active (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (live : activeProgress before.progress = true) :
    InactiveBackingExtension state {state with destinations := state.destinations.set! id after} := by
  intro index row found inactive
  have different : id ≠ index := by
    intro same
    subst index
    cases Option.some.inj (found.symm.trans present)
    exact Bool.noConfusion (live.symm.trans inactive)
  exact ⟨row, by simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different] using found, inactive, rfl⟩

private theorem inactive_replace_phase (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (backing : after.backing = before.backing)
    (phase : after.progress = before.progress ∨ after.progress = .abandoned ∨ after.progress = .cancelled) :
    InactiveBackingExtension state {state with destinations := state.destinations.set! id after} := by
  intro index row found inactive
  by_cases same : id = index
  · subst index
    cases Option.some.inj (found.symm.trans present)
    refine ⟨after, Array.getElem?_setIfInBounds_self_of_lt (Array.getElem?_eq_some_iff.mp present).1, ?_, backing⟩
    rcases phase with same | abandoned | cancelled
    · simpa only [same] using inactive
    · simp only [abandoned, activeProgress]
    · simp only [cancelled, activeProgress]
  · exact ⟨row, by simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same] using found, inactive, rfl⟩

private theorem inactive_push (state : ConstructionState) (added : PendingDestination) :
    InactiveBackingExtension state {state with destinations := state.destinations.push added} := by
  intro id row present inactive
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  exact ⟨row, by simpa only [Array.getElem?_push, Nat.ne_of_lt inside, ↓reduceIte] using present, inactive, rfl⟩

private theorem RowsFrame.refl (state : ConstructionState) : RowsFrame state state :=
  ⟨.refl state, inactiveBackingExtension_refl state, replacementSupportExtension_refl _⟩

private theorem RowsFrame.trans {before middle after : ConstructionState}
    (firstMetadata : ReservationMetadataFrame before middle) (secondMetadata : ReservationMetadataFrame middle after)
    (first : RowsFrame before middle) (second : RowsFrame middle after) : RowsFrame before after :=
  ⟨OwnershipLinkRowsFrame.trans firstMetadata secondMetadata first.1 second.1,
    inactiveBackingExtension_trans before middle after first.2.1 second.2.1,
    support_rows_trans before middle after firstMetadata.destinations first.2.2 second.2.2⟩

private theorem ForwardFrame.refl (state : ConstructionState) : ForwardFrame state state :=
  ⟨.refl state, id⟩

private theorem ForwardFrame.trans {before middle after : ConstructionState}
    (firstMetadata : ReservationMetadataFrame before middle) (secondMetadata : ReservationMetadataFrame middle after)
    (first : ForwardFrame before middle) (second : ForwardFrame middle after) : ForwardFrame before after :=
  ⟨RowsFrame.trans firstMetadata secondMetadata first.1 second.1, fun links => second.2 (first.2 links)⟩

private theorem rows_same (before after : ConstructionState) (same : after.destinations = before.destinations) :
    RowsFrame before after := ⟨ownershipLinkRowsFrame_same_rows before after same, inactive_same_rows before after same,
    support_rows before after (fun id _ supported => replacementSupported_congr_destinations after before same.symm id supported)⟩

private theorem forward_same (before after : ConstructionState) (same : after.destinations = before.destinations) :
    ForwardFrame before after :=
  ⟨rows_same before after same, (ownershipForwardRowsFrame_same_rows before after same).2⟩

private theorem rows_mutable (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (sameUse : after.use = before.use) (backing : OwnershipLinkBacking before after)
    (mutable : ¬ ReservationStableProgress before.progress) :
    RowsFrame state {state with destinations := state.destinations.set! id after} := by
  refine ⟨ownershipLinkRowsFrame_replace_mutable state id before after present sameUse backing mutable,
    inactive_replace_active state id before after present ?_, ?_⟩
  · cases progress : before.progress <;> simp_all [ReservationStableProgress, activeProgress]
  · apply support_rows state _
    intro index _ supported
    apply replacementSupported_replace_back state id before after present
      (fun parent use => sameUse.symm.trans use) _ index supported
    intro _
    cases progress : before.progress <;> simp_all [ReservationStableProgress, activeProgress]

private theorem rows_terminal (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (sameUse : after.use = before.use) (backing : OwnershipLinkBacking before after)
    (terminal : ∀ count selected, after.progress ≠ .exiting count selected)
    (sameBacking : after.backing = before.backing)
    (phase : after.progress = before.progress ∨ after.progress = .abandoned ∨ after.progress = .cancelled) :
    RowsFrame state {state with destinations := state.destinations.set! id after} :=
  ⟨ownershipLinkRowsFrame_replace_terminal state id before after present sameUse backing terminal sameBacking phase,
    inactive_replace_phase state id before after present sameBacking phase, by
      apply support_rows state _
      intro index _ supported
      apply replacementSupported_replace_back state id before after present
        (fun parent use => sameUse.symm.trans use) _ index supported
      intro live
      rcases phase with same | abandoned | cancelled
      · simpa only [same] using live
      · simp only [abandoned, activeProgress, Bool.false_eq_true] at live
      · simp only [cancelled, activeProgress, Bool.false_eq_true] at live⟩

private theorem rows_push (state : ConstructionState) (row : PendingDestination)
    (notReplacement : ∀ parent, row.use ≠ .replacement parent) :
    RowsFrame state {state with destinations := state.destinations.push row} :=
  ⟨ownershipLinkRowsFrame_push state row notReplacement, inactive_push state row,
    support_rows state _ (replacementSupported_push_back state row notReplacement)⟩

private theorem rows_push_mutable (state : ConstructionState) (id : DestinationId)
    (before after added : PendingDestination) (present : state.destinations[id]? = some before)
    (sameUse : after.use = before.use) (backing : OwnershipLinkBacking before after)
    (mutable : ¬ ReservationStableProgress before.progress)
    (sameBacking : after.backing = before.backing)
    (addedParent : ∀ parent, added.use = .replacement parent →
      parent = id ∧ added.backing = before.backing ∧ ∃ count, after.progress = .exiting count state.destinations.size) :
    RowsFrame state {state with destinations := (state.destinations.push added).set! id after} := by
  refine ⟨ownershipLinkRowsFrame_push_replace_mutable state id before after added present sameUse backing mutable sameBacking addedParent, ?_, ?_⟩
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have pushed : (state.destinations.push added)[id]? = some before := by
    simpa only [Array.getElem?_push, Nat.ne_of_lt inside, ↓reduceIte] using present
  · apply inactiveBackingExtension_trans state {state with destinations := state.destinations.push added} _ (inactive_push state added)
    apply inactive_replace_active _ id before after pushed
    cases progress : before.progress <;> simp_all [ReservationStableProgress, activeProgress]
  · apply support_rows state _
    apply replacementSupported_push_replace_back state id before after added present sameUse
    · cases progress : before.progress <;> simp_all [ReservationStableProgress, activeProgress]
    · intro parent use
      exact (addedParent parent use).1

private theorem forward_leaf (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (sameUse : after.use = before.use) (backing : OwnershipLinkBacking before after)
    (mutable : ¬ ReservationStableProgress before.progress) (leaf : OwnershipLeafProgress after.progress) :
    ForwardFrame state {state with destinations := state.destinations.set! id after} :=
  ⟨rows_mutable state id before after present sameUse backing mutable,
    (ownershipForwardRowsFrame_replace_leaf state id before after present sameUse backing mutable leaf).2⟩

private theorem forward_terminal (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (sameUse : after.use = before.use) (backing : OwnershipLinkBacking before after)
    (leaf : OwnershipLeafProgress after.progress)
    (sameBacking : after.backing = before.backing)
    (phase : after.progress = before.progress ∨ after.progress = .abandoned ∨ after.progress = .cancelled) :
    ForwardFrame state {state with destinations := state.destinations.set! id after} :=
  ⟨rows_terminal state id before after present sameUse backing
      (by intro count selected exiting; simp only [exiting, OwnershipLeafProgress] at leaf) sameBacking phase,
    (ownershipForwardRowsFrame_replace_terminal state id before after present sameUse backing leaf sameBacking phase).2⟩

private theorem forward_two_leaf (state : ConstructionState) (first second : DestinationId)
    (beforeFirst beforeSecond afterFirst afterSecond : PendingDestination)
    (firstPresent : state.destinations[first]? = some beforeFirst)
    (secondPresent : state.destinations[second]? = some beforeSecond) (different : first ≠ second)
    (firstUse : afterFirst.use = beforeFirst.use) (secondUse : afterSecond.use = beforeSecond.use)
    (firstBacking : OwnershipLinkBacking beforeFirst afterFirst)
    (secondBacking : OwnershipLinkBacking beforeSecond afterSecond)
    (firstMutable : ¬ ReservationStableProgress beforeFirst.progress)
    (secondMutable : ¬ ReservationStableProgress beforeSecond.progress)
    (firstLeaf : OwnershipLeafProgress afterFirst.progress) (secondLeaf : OwnershipLeafProgress afterSecond.progress) :
    ForwardFrame state {state with destinations := (state.destinations.set! first afterFirst).set! second afterSecond} := by
  have old := ownershipForwardRowsFrame_two_leaf state first second beforeFirst beforeSecond afterFirst afterSecond
    firstPresent secondPresent different firstUse secondUse firstBacking secondBacking firstMutable secondMutable firstLeaf secondLeaf
  have secondFound : (state.destinations.set! first afterFirst)[second]? = some beforeSecond := by
    simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different] using secondPresent
  refine ⟨⟨old.1, ?_, ?_⟩, old.2⟩
  · exact inactiveBackingExtension_trans state _ _
      (rows_mutable state first beforeFirst afterFirst firstPresent firstUse firstBacking firstMutable).2.1
      (rows_mutable {state with destinations := state.destinations.set! first afterFirst} second
        beforeSecond afterSecond secondFound secondUse secondBacking secondMutable).2.1
  · exact support_rows_trans state _ _ (by simp)
      (rows_mutable state first beforeFirst afterFirst firstPresent firstUse firstBacking firstMutable).2.2
      (rows_mutable {state with destinations := state.destinations.set! first afterFirst} second
        beforeSecond afterSecond secondFound secondUse secondBacking secondMutable).2.2

private theorem RowsFrame.children {before after : ConstructionState} (frame : RowsFrame before after) :
    OwnershipChildSourceExtension before after := frame.1.children

private theorem RowsFrame.exiting {before after : ConstructionState} (frame : RowsFrame before after) :
    OwnershipExitingRowsFrame before after := frame.1.exiting

private theorem RowsFrame.authority {before after : ConstructionState} (frame : RowsFrame before after) :
    SupportedReplacementAuthority before → SupportedReplacementAuthority after := frame.1.authority

open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

local syntax "ownership_rows_split_if" : tactic
elab_rules : tactic
  | `(tactic| ownership_rows_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no ownership row condition to split"
      return [yes.mvarId, no.mvarId]

private theorem reserveStorage_ownership_rows (bytes : ByteArray) (count : Nat) (state : ConstructionState) :
    RowsFrame state (reserveStorage bytes count state).finalState := rows_same state _ rfl

private theorem adaptDestinationType_ownership_rows (state : ConstructionState) (id : DestinationId)
    (ty : Construct.Ty) : RowsFrame state (adaptDestinationType id ty state).finalState := by
  simp only [adaptDestinationType, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some row =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          cases progress : row.progress <;> try simp only [progress] <;> try exact .refl state
          all_goals
            repeat' first
              | exact .refl state
              | solve
                | refine rows_mutable state id row _ present ?_ ?_ ?_
                  · rfl
                  · cases use : row.use <;> simp [OwnershipLinkBacking, use]
                  · simp [ReservationStableProgress, progress]
              | simp only [replaceDestination_result, inside, ↓reduceIte, bind, pure,
                  ConstructionM.fail, ConstructionResult.finalState]
              | ownership_rows_split_if
              | split

private theorem restoreReceivingLayout_ownership_rows (state : ConstructionState) (id : DestinationId)
    (layout : ReceivingLayout) : RowsFrame state (restoreReceivingLayout id layout state).finalState := by
  simp only [restoreReceivingLayout, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some row =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          cases progress : row.progress <;> try simp only [progress] <;> try exact .refl state
          case built count =>
            repeat' first
              | exact .refl state
              | solve
                | refine rows_mutable state id row _ present ?_ ?_ ?_
                  · rfl
                  · cases use : row.use <;> simp [OwnershipLinkBacking, use]
                  · simp [ReservationStableProgress, progress]
              | simp only [replaceDestination_result, inside, ↓reduceIte, bind, pure,
                  ConstructionM.fail, ConstructionResult.finalState]
              | ownership_rows_split_if
              | split

private theorem abandonDestination_ownership_rows (state : ConstructionState) (id : DestinationId) :
    RowsFrame state (abandonDestination id state).finalState := by
  simp only [abandonDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some row =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          cases progress : row.progress <;> try simp only [progress] <;> try exact .refl state
          all_goals
            simp only [lookupStorage_result, bind]
            cases stored : state.storage[row.storage]? with
            | none => exact .refl state
            | some storage =>
                have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
                simp only [stored, replaceStorage_result, replaceDestination_result,
                  storageInside, inside, ↓reduceIte, bind, pure, emit_result, ConstructionResult.finalState]
                refine rows_terminal state id row _ present ?_ ?_ ?_ rfl (Or.inr (Or.inl rfl))
                · rfl
                · cases use : row.use <;> simp [OwnershipLinkBacking, use]
                · intro count selected
                  simp

private theorem finishDestination_ownership_rows (state : ConstructionState) (id : DestinationId)
    (bounded : DestinationLifecycleInvariant state) :
    RowsFrame state (finishDestination id state).finalState := by
  simp only [finishDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some row =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          have storageInside := (bounded.2.2.1 id row present).1
          cases progress : row.progress <;> try simp only [progress] <;> try exact .refl state
          case «open» count =>
            have finished := rows_mutable state id row
              { row with progress := .built count } present rfl
              (by cases use : row.use <;> simp [OwnershipLinkBacking, use])
              (by simp [ReservationStableProgress, progress])
            have storedFinished : ∀ storage : ReceivingStorage,
                RowsFrame state { state with
                  storage := state.storage.set! row.storage storage
                  destinations := state.destinations.set! id { row with progress := .built count } } :=
              fun _ => finished
            cases layout : row.layout <;> simp only [layout]
            all_goals
              simp only [layout] at finished storedFinished
              cases stored : state.storage[row.storage]?
              all_goals
                repeat' first
                  | exact .refl state
                  | exact finished
                  | exact storedFinished _
                  | simp only [lookupStorage_result, stored, replaceStorage_result,
                      replaceDestination_result, inside, storageInside, ↓reduceIte, pure, bind,
                      ConstructionM.fail, ConstructionResult.finalState]
                  | ownership_rows_split_if
                  | split


local syntax "ownership_header_split_if" : tactic
elab_rules : tactic
  | `(tactic| ownership_header_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no ownership header condition to split"
      return [yes.mvarId, no.mvarId]

private theorem removeConstructionHeader_ownership_rows (id : DestinationId)
    (state : ConstructionState) :
    RowsFrame state (removeConstructionHeader id state).finalState := by
  simp only [removeConstructionHeader, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          cases progress : destination.progress <;> (try simp only [progress]) <;> try exact .refl state
          case built count =>
            have removed : ∀ storage : ReceivingStorage,
                RowsFrame state { state with
                  storage := state.storage.set! destination.storage storage
                  destinations := state.destinations.set! id { destination with layout := .elements, writeEnd := destination.writeEnd - 4 },
                  events := state.events ++ [.relocate id .headerRemoval] } := by
              intro storage
              refine rows_mutable state id destination _ present ?_ ?_ ?_
              · rfl
              · cases use : destination.use <;> simp [OwnershipLinkBacking, use]
              · simp [progress, ReservationStableProgress]
            simp only [progress] at removed
            cases stored : state.storage[destination.storage]? with
            | none =>
                repeat' first
                  | simp only [lookupStorage_result, stored, bind, ConstructionM.fail,
                      ConstructionResult.finalState]
                  | ownership_header_split_if
                  | exact .refl state
            | some receiving =>
              have bound := (Array.getElem?_eq_some_iff.mp stored).choose
              repeat' first
                | simp only [lookupStorage_result, stored, replaceStorage_result,
                    replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                    ConstructionM.fail, emit_result, ConstructionResult.finalState]
                | ownership_header_split_if
                | exact .refl state
                | exact removed _



private theorem prepareNamedBinding_ownership_rows (id : DestinationId)
    (localType : Construct.Ty) (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    RowsFrame state (prepareNamedBinding id localType state).finalState := by
  simp only [prepareNamedBinding, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have bound := (valid.2.2.1 id destination present).1
          cases progress : destination.progress <;> (try simp only [progress]) <;> try exact .refl state
          case «open» count =>
            cases count <;> try exact .refl state
            case zero =>
              have prepared : ∀ (storage : Array ReceivingStorage), storage.size = state.storage.size →
                  ∀ (layout : ReceivingLayout) (writeEnd : Nat),
                  RowsFrame state { state with storage := storage, destinations := state.destinations.set! id { destination with capability := { destination.capability with logicalType := localType }, layout := layout, writeEnd := writeEnd } } := by
                intro storage size layout writeEnd
                refine rows_mutable state id destination _ present ?_ ?_ ?_
                · rfl
                · cases use : destination.use <;> simp [OwnershipLinkBacking, use]
                · simp [progress, ReservationStableProgress]
              simp only [progress] at prepared
              cases stored : state.storage[destination.storage]?
              all_goals
                repeat' first
                  | simp only [lookupStorage_result, stored, replaceStorage_result,
                      replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                      ConstructionM.fail, emit_result, ConstructionResult.finalState]
                  | ownership_header_split_if
                  | exact .refl state
                  | exact prepared _ (by simp) _ _



private theorem truncateConstructionStorage_ownership_rows (storageId : StorageId)
    (start finish count : Nat) (owner : Option DestinationId) (retainSlots : Bool)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    RowsFrame state
      (truncateConstructionStorage storageId start finish count owner retainSlots state).finalState := by
  simp only [truncateConstructionStorage, lookupStorage_result, bind]
  cases stored : state.storage[storageId]? with
  | none => exact .refl state
  | some storage =>
      simp only [stored]
      have bound := (Array.getElem?_eq_some_iff.mp stored).choose
      have storageChanged : ∀ value : ReceivingStorage,
          RowsFrame state { state with storage := state.storage.set! storageId value } := by
        intro value
        exact .refl state
      cases owner with
      | none =>
          repeat' first
            | simp only [ConstructionM.get, replaceStorage_result, bound, ↓reduceIte,
                bind, pure, ConstructionM.fail, ConstructionResult.finalState]
            | ownership_header_split_if
            | exact .refl state
            | exact storageChanged _
      | some id =>
          cases present : state.destinations[id]? with
          | none =>
              repeat' first
                | simp only [ConstructionM.get, writableDestination_result, present,
                    ↓reduceIte, bind, pure, ConstructionM.fail, ConstructionResult.finalState]
                | ownership_header_split_if
                | exact .refl state
          | some destination =>
              cases allowed : destinationCanWrite state id with
              | false =>
                  repeat' first
                    | simp only [ConstructionM.get, writableDestination_result, present, allowed,
                        ↓reduceIte, bind, pure, ConstructionM.fail, ConstructionResult.finalState]
                    | ownership_header_split_if
                    | exact .refl state
              | true =>
                  have inside := (Array.getElem?_eq_some_iff.mp present).choose
                  have capId := valid.2.1 id destination present
                  cases progress : destination.progress <;> (try simp only [progress])
                  all_goals
                    try solve | repeat' first
                      | simp only [ConstructionM.get, writableDestination_result, present, allowed,
                          progress, ↓reduceIte, bind, pure, ConstructionM.fail, ConstructionResult.finalState]
                      | ownership_header_split_if
                      | exact .refl state
                  case built oldCount =>
                    have truncated : ∀ value : ReceivingStorage,
                        RowsFrame state { state with storage := state.storage.set! storageId value, destinations := state.destinations.set! id { destination with progress := .built count, writeEnd := finish } } := by
                      intro value
                      refine rows_mutable state id destination _ present ?_ ?_ ?_
                      · rfl
                      · cases use : destination.use <;> simp [OwnershipLinkBacking, use]
                      · simp [progress, ReservationStableProgress]
                    repeat' first
                      | simp only [ConstructionM.get, writableDestination_result, present, allowed,
                          progress, capId, replaceStorage_result, replaceDestination_result,
                          bound, inside, ↓reduceIte, bind, pure, ConstructionM.fail,
                          ConstructionResult.finalState]
                      | ownership_header_split_if
                      | exact .refl state
                      | exact truncated _



local syntax "ownership_write_split_if" : tactic
elab_rules : tactic
  | `(tactic| ownership_write_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no ownership write condition to split"
      return [yes.mvarId, no.mvarId]

set_option maxHeartbeats 800000 in
private theorem writeElement_ownership_rows (id : DestinationId) (bytes : ByteArray)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    RowsFrame state (writeElement id bytes state).finalState := by
  simp only [writeElement, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have bound := (valid.2.2.1 id destination present).1
          cases progress : destination.progress <;> (try simp only [progress]) <;> try exact .refl state
          case «open» count =>
            have committed : ∀ storage : ReceivingStorage,
                RowsFrame state { state with
                  storage := state.storage.set! destination.storage storage
                  destinations := state.destinations.set! id { destination with progress := .open (count + 1), writeEnd := destination.writeEnd + bytes.size },
                  events := state.events ++ [.write id count] } := by
              intro storage
              refine rows_mutable state id destination _ present ?_ ?_ ?_
              · rfl
              · cases use : destination.use <;> simp [OwnershipLinkBacking, use]
              · simp [progress, ReservationStableProgress]
            cases stored : state.storage[destination.storage]? with
            | none => simp only [lookupStorage_result, stored, bind]; exact .refl state
            | some storage =>
                simp only [lookupStorage_result, stored, bind]
                ownership_write_split_if
                · exact .refl state
                · try simp only [pure, bind, ConstructionM.fail, ConstructionResult.finalState]
                  cases layout : (destination.adaptation.map (·.layout)).getD destination.layout <;>
                    simp only [layout]
                  all_goals
                    repeat' first
                      | simp only [pure, bind, ConstructionM.fail, ConstructionResult.finalState]
                      | ownership_write_split_if
                    all_goals try exact .refl state
                    all_goals
                      cases use : destination.use <;> simp only [use]
                      all_goals
                        try solve | repeat' first
                            | simp_all only [lookupDestination_result, lookupStorage_result, replaceStorage_result,
                                replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                ConstructionM.fail, emit_result, ConstructionResult.finalState]
                            | ownership_write_split_if
                            | exact .refl state
                            | exact committed _
                      case child parentId =>
                        cases parentFound : state.destinations[parentId]? <;>
                          simp only [lookupDestination_result, parentFound, bind]
                        · repeat' first
                            | simp_all only [↓reduceIte, pure, bind, ConstructionM.fail, ConstructionResult.finalState]
                            | ownership_write_split_if
                            | exact .refl state
                        · rename_i parent
                          cases parentLayout : parent.layout <;> (try simp only [parentLayout])
                          all_goals
                            try solve | repeat' first
                                | simp_all only [lookupDestination_result, lookupStorage_result, replaceStorage_result,
                                    replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                    ConstructionM.fail, emit_result, ConstructionResult.finalState]
                                | ownership_write_split_if
                                | exact .refl state
                                | exact committed _
                          case limited capacity slotBytes =>
                            cases parentProgress : parent.progress <;> (try simp only [parentProgress])
                            all_goals
                              try solve | repeat' first
                                | simp_all only [lookupDestination_result, lookupStorage_result, replaceStorage_result,
                                    replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                    ConstructionM.fail, emit_result, ConstructionResult.finalState]
                                | ownership_write_split_if
                                | exact .refl state
                                | exact committed _
                            case suspended parentCount child =>
                              cases parentBacking : parent.backing <;> (try simp only [parentBacking])
                              all_goals
                                try solve | repeat' first
                                  | simp_all only [lookupDestination_result, lookupStorage_result, replaceStorage_result,
                                      replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                      ConstructionM.fail, emit_result, ConstructionResult.finalState]
                                  | ownership_write_split_if
                                  | exact .refl state
                                  | exact committed _
                              case direct parentStorage =>
                                cases backing : destination.backing <;> (try simp only [backing])
                                all_goals
                                  repeat' first
                                    | simp_all only [lookupDestination_result, lookupStorage_result, replaceStorage_result,
                                        replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                        ConstructionM.fail, emit_result, ConstructionResult.finalState]
                                    | ownership_write_split_if
                                    | exact .refl state
                                    | exact committed _


local syntax "ownership_stage_split_if" : tactic
elab_rules : tactic
  | `(tactic| ownership_stage_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no ownership stage condition to split"
      return [yes.mvarId, no.mvarId]

set_option maxHeartbeats 1000000 in
private theorem stageDestination_ownership_rows (state : ConstructionState) (id : DestinationId)
    : RowsFrame state (stageDestination id state).finalState := by
  simp only [stageDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some row =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          cases progress : row.progress <;> try simp only [progress] <;> try exact .refl state
          case «open» count =>
            cases count <;> try simp only <;> try exact .refl state
            cases layout : row.layout <;> try simp only [layout] <;> try exact .refl state
            cases backing : row.backing <;> try simp only [backing] <;> try exact .refl state
            cases known : row.knownCount <;> try simp only [known] <;> try exact .refl state
            cases use : row.use <;> try simp only [use] <;> try exact .refl state
            repeat' first
              | solve
                | simp only [← progress, ← layout, ← known, ← use]
                  refine rows_mutable state id row _ present ?_ ?_ ?_
                  · rfl
                  · simp [OwnershipLinkBacking, use, backing, DestinationBacking.receiverStorage]
                  · simp [ReservationStableProgress, progress]
              | simp only [reserveStorage, ConstructionM.get, ConstructionM.set, replaceDestination_result,
                  inside, ↓reduceIte, emit_result, bind, pure, ConstructionResult.finalState]
              | ownership_stage_split_if
              | split



local syntax "allocation_split_if" : tactic
elab_rules : tactic
  | `(tactic| allocation_split_if) =>
      Lean.Elab.Tactic.liftMetaTactic fun goal => do
        let some (yes, no) ← Lean.Meta.splitIfTarget? goal
          | Lean.throwError "no allocation condition to split"
        return [yes.mvarId, no.mvarId]

private theorem ownership_allocate_child (state : ConstructionState) (parentId : DestinationId)
    (parent child : PendingDestination) (count : Nat) (events : List ConstructionEvent)
    (storage : Array ReceivingStorage) (size : storage.size = state.storage.size)
    (present : state.destinations[parentId]? = some parent)
    (progress : parent.progress = .open count ∨ parent.progress = .built count)
    (correct : child.capability.id = state.destinations.size)
    (use : child.use = .child parentId)
    (writeStorage : child.storage < state.storage.size)
    (receiverStorage : child.backing.receiverStorage < state.storage.size)
    (other : ∀ index, index ≠ state.destinations.size → destinationObservations index events = [])
    (initial : ∃ phase,
      runDestinationTrace state.destinations.size .unseen events = some phase ∧
        phase.matchesDestination child)
    (valid : DestinationLifecycleInvariant state) :
    RowsFrame state { state with
      storage := storage
      destinations := (state.destinations.push child).set! parentId
        { parent with progress := .suspended count state.destinations.size }
      events := state.events ++ events } := by
  refine rows_push_mutable state parentId parent
    { parent with progress := .suspended count state.destinations.size } child present rfl ?_ ?_ rfl ?_
  · cases parentUse : parent.use <;> simp [OwnershipLinkBacking, parentUse]
  · intro stable
    rcases progress with opened | built <;> simp_all [ReservationStableProgress]
  · intro target replacement
    simp [use] at replacement

private theorem ownership_allocate_replacement (state : ConstructionState) (parentId : DestinationId)
    (parent child : PendingDestination) (count : Nat) (storage : Array ReceivingStorage)
    (size : storage.size = state.storage.size)
    (present : state.destinations[parentId]? = some parent)
    (progress : parent.progress = .open count ∨ parent.progress = .built count ∨
      ∃ nested, parent.progress = .suspended count nested)
    (correct : child.capability.id = state.destinations.size)
    (use : child.use = .replacement parentId)
    (backing : child.backing = parent.backing)
    (writeStorage : child.storage < state.storage.size)
    (receiverStorage : child.backing.receiverStorage < state.storage.size)
    (initial : ∃ phase,
      runDestinationTrace state.destinations.size .unseen [.begin state.destinations.size] = some phase ∧
        phase.matchesDestination child)
    (valid : DestinationLifecycleInvariant state) :
    RowsFrame state { state with
      storage := storage
      destinations := (state.destinations.push child).set! parentId
        { parent with progress := .exiting count state.destinations.size }
      events := state.events ++ [.begin state.destinations.size] } := by
  refine rows_push_mutable state parentId parent
    { parent with progress := .exiting count state.destinations.size } child present rfl ?_ ?_ rfl ?_
  · cases parentUse : parent.use <;> simp [OwnershipLinkBacking, parentUse]
  · intro stable
    rcases progress with opened | built | ⟨nested, suspended⟩ <;>
      simp_all [ReservationStableProgress]
  · intro target replacement
    have equal := DestinationUse.replacement.inj (use.symm.trans replacement)
    exact ⟨equal.symm, backing, count, rfl⟩

private theorem openChild_ownership_rows (parentId : DestinationId) (logicalType : Construct.Ty)
    (layout : ReceivingLayout) (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    RowsFrame state (openChild parentId logicalType layout state).finalState := by
  simp only [openChild, writableDestination_result, bind]
  cases present : state.destinations[parentId]? with
  | none => exact .refl state
  | some parent =>
      simp only [present]
      cases allowed : destinationCanWrite state parentId with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have insideAfter := Nat.lt_succ_of_lt inside
          have storageInside := (valid.2.2.1 parentId parent present).1
          cases progress : parent.progress <;> try simp only [progress] <;> try exact .refl state
          case «open» count =>
            simp only [lookupStorage_result, bind]
            cases stored : state.storage[parent.storage]? with
            | none => exact .refl state
            | some receiving =>
                simp only [stored]
                repeat' first
                  | exact .refl state
                  | solve
                    | apply ownership_allocate_child state parentId parent _ count
                        [.begin state.destinations.size] _
                      · simp [Array.set!_eq_setIfInBounds]
                      · exact present
                      · exact Or.inl progress
                      · rfl
                      · rfl
                      · simpa only [PendingDestination.storage, DestinationBacking.writeStorage] using storageInside
                      · simpa only [DestinationBacking.receiverStorage] using storageInside
                      · intro index different
                        simp [destinationObservations, observeDestination, Ne.symm different]
                      · refine ⟨.live false false, ?_, ?_⟩
                        · simp [runDestinationTrace, destinationObservations, observeDestination,
                            runDestinationObservations, destinationTraceStep]
                        · simp [DestinationTracePhase.matchesDestination,
                            DestinationTracePhase.matchesProgress]
                      · exact valid
                  | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                      replaceDestination_result, replaceStorage_result, emit_result,
                      Array.size_push, insideAfter, storageInside, ↓reduceIte,
                      bind, pure, ConstructionResult.finalState]
                  | allocation_split_if
                  | split

private theorem openElementExtension_ownership_rows (parentId : DestinationId) (logicalType : Construct.Ty)
    (layout : ReceivingLayout) (knownCount : Option Nat) (receiverLoc : Core.Loc) (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    RowsFrame state (openElementExtension parentId logicalType layout knownCount receiverLoc state).finalState := by
  simp only [openElementExtension, writableDestination_result, bind]
  cases present : state.destinations[parentId]? with
  | none => exact .refl state
  | some parent =>
      simp only [present]
      cases allowed : destinationCanWrite state parentId with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have insideAfter := Nat.lt_succ_of_lt inside
          have storageInside := (valid.2.2.1 parentId parent present).1
          cases progress : parent.progress <;> try simp only [progress] <;> try exact .refl state
          case built count =>
            simp only [lookupStorage_result, bind]
            cases stored : state.storage[parent.storage]? with
            | none =>
                have outside := Array.getElem?_eq_none_iff.mp stored
                exact False.elim (Nat.not_le_of_lt storageInside outside)
            | some receiving =>
                try simp only [stored]
                cases parentLayout : parent.layout <;> cases parentBacking : parent.backing
                all_goals repeat' first
                  | exact .refl state
                  | solve
                    | simp only [← parentLayout, ← parentBacking]
                      apply ownership_allocate_child state parentId parent _ count
                        [.begin state.destinations.size] _
                      · simp [Array.set!_eq_setIfInBounds]
                      · exact present
                      · exact Or.inr progress
                      · rfl
                      · rfl
                      · simpa only [PendingDestination.storage, DestinationBacking.writeStorage] using storageInside
                      · simpa only [DestinationBacking.receiverStorage] using storageInside
                      · intro index different
                        simp [destinationObservations, observeDestination, Ne.symm different]
                      · refine ⟨.live false false, ?_, ?_⟩
                        · simp [runDestinationTrace, destinationObservations, observeDestination,
                            runDestinationObservations, destinationTraceStep]
                        · simp [DestinationTracePhase.matchesDestination,
                            DestinationTracePhase.matchesProgress]
                      · exact valid
                  | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                      replaceDestination_result, replaceStorage_result, emit_result,
                      Array.size_push, insideAfter, storageInside, stored, parentLayout, parentBacking, ↓reduceIte,
                      bind, pure, ConstructionResult.finalState]
                  | allocation_split_if
                  | split


private theorem openExitReplacement_ownership_rows (parentId : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    RowsFrame state (openExitReplacement parentId state).finalState := by
  simp only [openExitReplacement, writableDestination_result, bind]
  cases present : state.destinations[parentId]? with
  | none => exact .refl state
  | some parent =>
      simp only [present]
      cases allowed : destinationCanWrite state parentId with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have insideAfter := Nat.lt_succ_of_lt inside
          have storageInside := (valid.2.2.1 parentId parent present).1
          cases progress : parent.progress <;> try simp only [progress] <;> try exact .refl state
          all_goals
            try simp only [pure, bind]
            simp only [lookupStorage_result, bind]
            cases stored : state.storage[parent.storage]? with
            | none => exact .refl state
            | some receiving =>
                simp only [stored]
                repeat' first
                  | exact .refl state
                  | solve
                    | first
                      | apply ownership_allocate_replacement state parentId parent _ _ _ _ present (Or.inl progress)
                      | apply ownership_allocate_replacement state parentId parent _ _ _ _ present (Or.inr (Or.inl progress))
                      | apply ownership_allocate_replacement state parentId parent _ _ _ _ present (Or.inr (Or.inr ⟨_, progress⟩))
                      · rfl
                      · rfl
                      · rfl
                      · exact storageInside
                      · exact (valid.2.2.1 parentId parent present).2
                      · refine ⟨.live false false, ?_, ?_⟩
                        · simp [runDestinationTrace, destinationObservations, observeDestination,
                            runDestinationObservations, destinationTraceStep]
                        · simp [DestinationTracePhase.matchesDestination,
                            DestinationTracePhase.matchesProgress]
                      · exact valid
                      · simp [Array.set!_eq_setIfInBounds]
                  | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                      replaceDestination_result, replaceStorage_result, emit_result,
                      Array.size_push, insideAfter, storageInside, ↓reduceIte,
                      bind, pure, ConstructionResult.finalState]
                  | allocation_split_if
                  | split


set_option maxHeartbeats 2000000 in
private theorem openExtension_ownership_rows (parentId : DestinationId)
    (request : ConstructionRequest) (knownCount : Option Nat)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    RowsFrame state (openExtension parentId request knownCount state).finalState := by
  simp only [openExtension, writableDestination_result, bind]
  cases present : state.destinations[parentId]? with
  | none => exact .refl state
  | some parent =>
      simp only [present]
      cases allowed : destinationCanWrite state parentId with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have insideAfter := Nat.lt_succ_of_lt inside
          have storageInside := (valid.2.2.1 parentId parent present).1
          let reserved : ConstructionState := { state with storage := state.storage.push ⟨ByteArray.empty, 0⟩ }
          have reservedValid : DestinationLifecycleInvariant reserved :=
            reserveStorage_destination_lifecycle_invariant ByteArray.empty 0 state valid
          have reservedFrame : RowsFrame state reserved := reserveStorage_ownership_rows ByteArray.empty 0 state
          cases progress : parent.progress <;> try simp only [progress] <;> try exact .refl state
          case built count =>
            simp only [pure, lookupStorage_result, bind]
            cases stored : state.storage[parent.storage]? with
            | none => exact .refl state
            | some receiving =>
                try simp only [stored]
                cases parentLayout : parent.layout <;> cases parentBacking : parent.backing <;> cases knownCount
                all_goals repeat' first
                  | exact .refl state
                  | exact reservedFrame
                  | solve
                    | simp only [← parentLayout, ← parentBacking]
                      apply ownership_allocate_child state parentId parent _ count
                        [.begin state.destinations.size] _
                      · rfl
                      · exact present
                      · exact Or.inr progress
                      · rfl
                      · rfl
                      · simpa only [PendingDestination.storage, DestinationBacking.writeStorage] using storageInside
                      · simpa only [DestinationBacking.receiverStorage] using storageInside
                      · intro index different
                        simp [destinationObservations, observeDestination, Ne.symm different]
                      · refine ⟨.live false false, ?_, ?_⟩
                        · simp [runDestinationTrace, destinationObservations, observeDestination,
                            runDestinationObservations, destinationTraceStep]
                        · simp [DestinationTracePhase.matchesDestination,
                            DestinationTracePhase.matchesProgress]
                      · exact valid
                  | solve
                    | simp only [← parentLayout, ← parentBacking]
                      apply ownership_allocate_child reserved parentId parent _ count
                        [.begin state.destinations.size, .stage state.destinations.size] _
                      · rfl
                      · exact present
                      · exact Or.inr progress
                      · rfl
                      · rfl
                      · simp [reserved, PendingDestination.storage, DestinationBacking.writeStorage]
                      · simpa only [reserved, Array.size_push, DestinationBacking.receiverStorage]
                          using Nat.lt.step storageInside
                      · intro index different
                        simp only [reserved] at different
                        simp [destinationObservations, observeDestination, Ne.symm different]
                      · refine ⟨.live true false, ?_, ?_⟩
                        · simp [reserved, runDestinationTrace, destinationObservations, observeDestination,
                            runDestinationObservations, destinationTraceStep]
                        · simp [DestinationTracePhase.matchesDestination,
                            DestinationTracePhase.matchesProgress]
                      · exact reservedValid
                  | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                      reserveStorage, replaceDestination_result, emit_result,
                      Array.size_push, insideAfter, storageInside, stored, parentLayout, parentBacking,
                      ↓reduceIte, bind, pure, ConstructionResult.finalState, List.append_assoc]
                  | allocation_split_if
                  | split

set_option maxHeartbeats 2000000 in
private theorem openDestinationDirect_ownership_rows (storageId : StorageId)
    (capability : Core.Destination Construct.Ty) (layout : ReceivingLayout) (knownCount : Option Nat)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    RowsFrame state (openDestinationDirect storageId capability layout knownCount state).finalState := by
  rw [openDestinationDirect_transition]
  simp only [lookupStorage_result, bind]
  cases stored : state.storage[storageId]? with
  | none => exact .refl state
  | some receiving =>
      simp only [stored]
      have storageInside := (Array.getElem?_eq_some_iff.mp stored).choose
      have allocated : ∀ (start writeEnd rollbackEnd : Nat) (storage : Array ReceivingStorage),
          storage.size = state.storage.size →
          RowsFrame state { state with
            storage := storage
            destinations := state.destinations.push
              ⟨{ capability with id := state.destinations.size, start := start }, .direct storageId,
                layout, .receiver, .open 0, writeEnd, rollbackEnd, knownCount, none⟩
            events := state.events ++ [.begin state.destinations.size] } := by
        intro start writeEnd rollbackEnd storage size
        exact rows_push state _ (by intro parent; simp)
      cases layout <;> cases knownCount
      all_goals repeat' first
        | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
            lookupStorage_result, stored, DestinationBacking.writeStorage,
            replaceStorage_result, storageInside, emit_result, Nat.lt_irrefl,
            ↓reduceIte, bind, pure, ConstructionResult.finalState]
        | allocation_split_if
        | exact .refl state
        | exact allocated _ _ _ _ (by simp)

set_option maxHeartbeats 2000000 in
private theorem openDestination_ownership_rows (storageId : StorageId)
    (capability : Core.Destination Construct.Ty) (layout : ReceivingLayout) (knownCount : Option Nat)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    RowsFrame state (openDestination storageId capability layout knownCount state).finalState := by
  cases layout with
  | packed =>
      simpa only [openDestination_transition, openDestinationDirect_transition] using
        openDestinationDirect_ownership_rows storageId capability .packed knownCount state valid
  | elements =>
      simpa only [openDestination_transition, openDestinationDirect_transition] using
        openDestinationDirect_ownership_rows storageId capability .elements knownCount state valid
  | fixed expected =>
      simpa only [openDestination_transition, openDestinationDirect_transition] using
        openDestinationDirect_ownership_rows storageId capability (.fixed expected) knownCount state valid
  | limited capacity slotBytes =>
      cases knownCount with
      | some count =>
          simpa only [openDestination_transition, openDestinationDirect_transition] using
            openDestinationDirect_ownership_rows storageId capability
              (.limited capacity slotBytes) (some count) state valid
      | none =>
          rw [openDestination_transition]
          simp only [lookupStorage_result, bind]
          cases stored : state.storage[storageId]? with
          | none => exact .refl state
          | some receiving =>
              simp only [stored]
              have storageInside := (Array.getElem?_eq_some_iff.mp stored).choose
              let reserved : ConstructionState := { state with storage := state.storage.push ⟨ByteArray.empty, 0⟩ }
              have reservedValid : DestinationLifecycleInvariant reserved :=
                reserveStorage_destination_lifecycle_invariant ByteArray.empty 0 state valid
              have reservedFrame : RowsFrame state reserved := reserveStorage_ownership_rows ByteArray.empty 0 state
              have allocated : ∀ (start writeEnd rollbackEnd : Nat) (storage : Array ReceivingStorage),
                  storage.size = reserved.storage.size →
                  RowsFrame state { reserved with
                    storage := storage
                    destinations := reserved.destinations.push
                      ⟨{ capability with id := state.destinations.size, start := start },
                        .staged storageId state.storage.size, .limited capacity slotBytes, .receiver,
                        .open 0, writeEnd, rollbackEnd, none, none⟩
                    events := state.events ++ [.begin state.destinations.size, .stage state.destinations.size] } := by
                intro start writeEnd rollbackEnd storage size
                exact rows_push state _ (by intro parent; simp)
              repeat' first
                | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                    reserveStorage, lookupStorage_result, DestinationBacking.writeStorage,
                    Array.getElem?_push_size, Nat.lt_irrefl,
                    replaceStorage_result, Array.size_push, Nat.lt_succ_self, emit_result,
                    ↓reduceIte, bind, pure, ConstructionResult.finalState, List.append_assoc]
                | allocation_split_if
                | exact .refl state
                | exact reservedFrame
                | exact allocated _ _ _ _ (by simp [reserved])



local syntax "attach_split_if" : tactic
elab_rules : tactic
  | `(tactic| attach_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no construction condition to split"
      return [yes.mvarId, no.mvarId]

private theorem ownership_attach_child (state : ConstructionState) (parentId childId count expected childCount : Nat)
    (parent child : PendingDestination)
    (parentFound : state.destinations[parentId]? = some parent)
    (childFound : state.destinations[childId]? = some child)
    (parentProgress : parent.progress = .suspended count expected)
    (childProgress : child.progress = .built childCount)
    (use : child.use = .child parentId) (valid : DestinationLifecycleInvariant state) :
    ForwardFrame state { state with
      destinations := (state.destinations.set! childId { child with progress := .attached childCount }).set! parentId { parent with progress := .open (count + 1), writeEnd := child.writeEnd }
      events := state.events ++ [.write parentId count] } := by
  have ordered : parentId < childId := by simpa only [use] using valid.2.2.2 childId child childFound
  refine forward_two_leaf state childId parentId child parent _ _
    childFound parentFound (Nat.ne_of_lt ordered).symm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · simp_all [OwnershipLinkBacking, DestinationBacking.receiverStorage]
  · cases parentUse : parent.use <;> simp [OwnershipLinkBacking, parentUse]
  · simp [ReservationStableProgress, childProgress]
  · simp [ReservationStableProgress, parentProgress]
  · trivial
  · trivial

private theorem attachChild_ownership_frame (parentId childId : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ForwardFrame state (attachChild parentId childId state).finalState := by
  simp only [attachChild, writableDestination_result, bind]
  cases parentFound : state.destinations[parentId]? with
  | none => exact .refl state
  | some parent =>
      simp only [parentFound]
      cases parentAllowed : destinationCanWrite state parentId with
      | false => exact .refl state
      | true =>
          simp only [parentAllowed]
          cases childFound : state.destinations[childId]? with
          | none => exact .refl state
          | some child =>
              simp only [childFound]
              cases childAllowed : destinationCanWrite state childId with
              | false => exact .refl state
              | true =>
                  simp only [childAllowed]
                  have parentInside := (Array.getElem?_eq_some_iff.mp parentFound).choose
                  have childInside := (Array.getElem?_eq_some_iff.mp childFound).choose
                  cases parentProgress : parent.progress <;> (try simp only [parentProgress]) <;> try exact .refl state
                  case suspended count expected =>
                    cases childProgress : child.progress <;> (try simp only [childProgress]) <;> try exact .refl state
                    case built childCount =>
                      cases use : child.use <;> (try simp only [use]) <;> try exact .refl state
                      case child owner =>
                        repeat' first
                          | simp only [replaceDestination_result, parentInside, childInside, Array.size_set!,
                              ↓reduceIte, pure, bind, ConstructionM.fail, emit_result, ConstructionResult.finalState]
                          | attach_split_if
                          | exact .refl state
                        have ownerEqual : owner = parentId := by simp_all
                        subst owner
                        simpa only [parentProgress, childProgress, use] using
                          ownership_attach_child state parentId childId count expected childCount parent child
                            parentFound childFound parentProgress childProgress use valid


set_option maxHeartbeats 1600000 in
private theorem attachElementExtension_ownership_frame (parentId childId : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ForwardFrame state (attachElementExtension parentId childId state).finalState := by
  simp only [attachElementExtension, writableDestination_result, bind]
  cases parentFound : state.destinations[parentId]? with
  | none => exact .refl state
  | some parent =>
      simp only [parentFound]
      cases parentAllowed : destinationCanWrite state parentId with
      | false => exact .refl state
      | true =>
          simp only [parentAllowed]
          cases childFound : state.destinations[childId]? with
          | none => exact .refl state
          | some child =>
              simp only [childFound]
              cases childAllowed : destinationCanWrite state childId with
              | false => exact .refl state
              | true =>
                  simp only [childAllowed]
                  have parentInside := (Array.getElem?_eq_some_iff.mp parentFound).choose
                  have childInside := (Array.getElem?_eq_some_iff.mp childFound).choose
                  have bound := (valid.2.2.1 parentId parent parentFound).1
                  cases parentProgress : parent.progress <;> (try simp only [parentProgress]) <;> try exact .refl state
                  case suspended count expected =>
                    cases childProgress : child.progress <;> (try simp only [childProgress]) <;> try exact .refl state
                    case built childCount =>
                      cases use : child.use <;> (try simp only [use]) <;> try exact .refl state
                      case child owner =>
                        cases backing : child.backing <;> (try simp only [backing]) <;> try exact .refl state
                        case direct storageId =>
                          by_cases adaptation : child.adaptation.isSome = true
                          · simp only [adaptation, ↓reduceIte, ConstructionM.fail, ConstructionResult.finalState]; exact .refl state
                          · simp only [adaptation, ↓reduceIte]
                            by_cases ownership : (expected != childId || owner != parentId || storageId != parent.storage || child.capability.request != .value || parent.capability.logicalType.element? != some child.capability.logicalType) = true
                            · simp only [ownership, ↓reduceIte, ConstructionM.fail, ConstructionResult.finalState]; exact .refl state
                            · simp only [ownership, ↓reduceIte]
                              have ownerEqual : owner = parentId := by
                                apply Classical.byContradiction
                                intro different
                                apply ownership
                                simp only [Bool.or_eq_true, bne_iff_ne]
                                exact Or.inl (Or.inl (Or.inl (Or.inr different)))
                              subst owner
                              have committed : ∀ storage : Array ReceivingStorage, storage.size = state.storage.size →
                                  ForwardFrame state { state with
                                    storage := storage
                                    destinations := (state.destinations.set! childId { child with progress := .attached childCount }).set! parentId { parent with progress := .built (count + 1), writeEnd := child.writeEnd }
                                    events := state.events ++ [.publish childId] } := by
                                intro storage size
                                have ordered : parentId < childId := by simpa only [use] using valid.2.2.2 childId child childFound
                                refine forward_two_leaf state childId parentId child parent _ _
                                  childFound parentFound (Nat.ne_of_lt ordered).symm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                                · rfl
                                · rfl
                                · simp_all [OwnershipLinkBacking, DestinationBacking.receiverStorage]
                                · cases parentUse : parent.use <;> simp [OwnershipLinkBacking, parentUse]
                                · simp [ReservationStableProgress, childProgress]
                                · simp [ReservationStableProgress, parentProgress]
                                · trivial
                                · trivial
                              simp only [parentProgress, childProgress, use, backing] at committed
                              cases stored : state.storage[parent.storage]?
                              all_goals
                                cases layout : parent.layout
                                all_goals simp only [layout] at committed
                                all_goals repeat' first
                                  | simp only [lookupStorage_result, stored, layout, replaceStorage_result,
                                      replaceDestination_result, parentInside, childInside, Array.size_set!, bound,
                                      ↓reduceIte, pure, bind, ConstructionM.fail, emit_result, ConstructionResult.finalState]
                                  | attach_split_if
                                  | exact .refl state
                                  | exact committed _ (by simp)


set_option maxHeartbeats 2400000 in
private theorem attachExtension_ownership_frame (parentId childId : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ForwardFrame state (attachExtension parentId childId state).finalState := by
  simp only [attachExtension, writableDestination_result, bind]
  cases parentFound : state.destinations[parentId]? with
  | none => exact .refl state
  | some parent =>
      simp only [parentFound]
      cases parentAllowed : destinationCanWrite state parentId with
      | false => exact .refl state
      | true =>
          simp only [parentAllowed]
          cases childFound : state.destinations[childId]? with
          | none => exact .refl state
          | some child =>
              simp only [childFound]
              cases childAllowed : destinationCanWrite state childId with
              | false => exact .refl state
              | true =>
                  simp only [childAllowed]
                  have parentInside := (Array.getElem?_eq_some_iff.mp parentFound).choose
                  have childInside := (Array.getElem?_eq_some_iff.mp childFound).choose
                  have bound := (valid.2.2.1 parentId parent parentFound).1
                  cases parentProgress : parent.progress <;> (try simp only [parentProgress]) <;> try exact .refl state
                  case suspended count expected =>
                    cases childProgress : child.progress <;> (try simp only [childProgress]) <;> try exact .refl state
                    case built childCount =>
                      cases use : child.use <;> (try simp only [use]) <;> try exact .refl state
                      case child owner =>
                        by_cases adaptation : child.adaptation.isSome = true
                        · simp only [adaptation, ↓reduceIte, ConstructionM.fail, ConstructionResult.finalState]; exact .refl state
                        · simp only [adaptation, ↓reduceIte]
                          by_cases ownership : (expected != childId || owner != parentId || child.backing.receiverStorage != parent.storage || child.layout != .elements) = true
                          · simp only [ownership, ↓reduceIte, ConstructionM.fail, ConstructionResult.finalState]; exact .refl state
                          · simp only [ownership, ↓reduceIte]
                            have ownerEqual : owner = parentId := by
                              apply Classical.byContradiction
                              intro different
                              apply ownership
                              simp only [Bool.or_eq_true, bne_iff_ne]
                              exact Or.inl (Or.inl (Or.inr different))
                            subst owner
                            cases childBacking : child.backing with
                            | direct receiver =>
                                have committed : ∀ storage : Array ReceivingStorage, storage.size = state.storage.size →
                                    ForwardFrame state { state with
                                      storage := storage
                                      destinations := (state.destinations.set! childId { child with progress := .attached childCount }).set! parentId { parent with progress := .built (count + childCount), writeEnd := child.writeEnd }
                                      events := state.events ++ [.publish childId] } := by
                                  intro storage size
                                  have ordered : parentId < childId := by simpa only [use] using valid.2.2.2 childId child childFound
                                  refine forward_two_leaf state childId parentId child parent _ _
                                    childFound parentFound (Nat.ne_of_lt ordered).symm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                                  · rfl
                                  · rfl
                                  · simp_all [OwnershipLinkBacking, DestinationBacking.receiverStorage]
                                  · cases parentUse : parent.use <;> simp [OwnershipLinkBacking, parentUse]
                                  · simp [ReservationStableProgress, childProgress]
                                  · simp [ReservationStableProgress, parentProgress]
                                  · trivial
                                  · trivial
                                simp only [parentProgress, childProgress, use, childBacking] at committed
                                cases stored : state.storage[parent.storage]?
                                all_goals
                                  cases layout : parent.layout <;> cases backing : parent.backing
                                  all_goals simp only [layout, backing] at committed
                                  all_goals repeat' first
                                    | simp only [lookupStorage_result, stored, layout, backing, childBacking, use, childProgress, parentProgress,
                                        replaceStorage_result, replaceDestination_result, parentInside, childInside, Array.size_set!, bound,
                                        ↓reduceIte, pure, bind, ConstructionM.fail, emit_result, ConstructionResult.finalState]
                                    | attach_split_if
                                    | exact .refl state
                                    | exact committed _ (by simp)
                            | staged receiver stageId =>
                                have stageBound : stageId < state.storage.size := by
                                  simpa only [childBacking, PendingDestination.storage, DestinationBacking.writeStorage] using (valid.2.2.1 childId child childFound).1
                                have committed : ∀ (storage : Array ReceivingStorage), storage.size = state.storage.size → ∀ stage : ReceivingStorage,
                                    ForwardFrame state { state with
                                      storage := storage
                                      destinations := (state.destinations.set! childId { child with
                                        backing := .direct parent.storage
                                        capability := { child.capability with start := parent.writeEnd }
                                        writeEnd := parent.writeEnd + stage.bytes.size
                                        progress := .attached childCount }).set! parentId { parent with progress := .built (count + childCount), writeEnd := parent.writeEnd + stage.bytes.size }
                                      events := (state.events ++ [.copy (.storage stageId []) childId]) ++ [.publish childId] } := by
                                  intro storage size stage
                                  have ordered : parentId < childId := by simpa only [use] using valid.2.2.2 childId child childFound
                                  refine forward_two_leaf state childId parentId child parent _ _
                                    childFound parentFound (Nat.ne_of_lt ordered).symm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                                  · rfl
                                  · rfl
                                  · simp_all [OwnershipLinkBacking, DestinationBacking.receiverStorage]
                                  · cases parentUse : parent.use <;> simp [OwnershipLinkBacking, parentUse]
                                  · simp [ReservationStableProgress, childProgress]
                                  · simp [ReservationStableProgress, parentProgress]
                                  · trivial
                                  · trivial
                                simp only [parentProgress, childProgress, use, childBacking] at committed
                                cases stored : state.storage[parent.storage]?
                                all_goals
                                  cases stageFound : state.storage[stageId]?
                                  all_goals
                                    cases layout : parent.layout <;> cases backing : parent.backing
                                    all_goals simp only [layout, backing] at committed
                                    all_goals repeat' first
                                      | simp only [lookupStorage_result, stored, stageFound, layout, backing, childBacking, use, childProgress, parentProgress,
                                          replaceStorage_result, replaceDestination_result, parentInside, childInside, Array.size_set!, Array.size_set!, bound, stageBound,
                                          ↓reduceIte, pure, bind, ConstructionM.fail, emit_result, ConstructionResult.finalState]
                                      | attach_split_if
                                      | exact .refl state
                                      | exact committed _ (by simp) _


private theorem publishElementDestination_ownership_frame (id : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ForwardFrame state (publishElementDestination id state).finalState := by
  simp only [publishElementDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          cases progress : destination.progress <;> (try simp only [progress]) <;> try exact .refl state
          case built count =>
            cases use : destination.use <;> (try simp only [use]) <;> try exact .refl state
            case receiver =>
              cases backing : destination.backing <;> (try simp only [backing]) <;> try exact .refl state
              case direct storageId =>
                have bound : storageId < state.storage.size := by
                  simpa only [backing, DestinationBacking.receiverStorage] using (valid.2.2.1 id destination present).2
                have committed : ∀ storage : ReceivingStorage,
                    ForwardFrame state { state with storage := state.storage.set! storageId storage, destinations := state.destinations.set! id { destination with progress := .published count }, events := state.events ++ [.publish id] } := by
                  intro storage
                  refine forward_leaf state id destination _ present ?_ ?_ ?_ ?_
                  · rfl
                  · simp [OwnershipLinkBacking, use]
                  · simp [progress, ReservationStableProgress]
                  · trivial
                simp only [backing, use] at committed
                cases stored : state.storage[storageId]?
                all_goals repeat' first
                  | simp only [lookupStorage_result, stored, replaceStorage_result,
                      replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                      ConstructionM.fail, emit_result, ConstructionResult.finalState]
                  | attach_split_if
                  | exact .refl state
                  | exact committed _



private theorem retireRepeatedSource_ownership_frame (parentId sourceId : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ForwardFrame state (retireRepeatedSource parentId sourceId state).finalState := by
  simp only [retireRepeatedSource, writableDestination_result, bind]
  cases parentFound : state.destinations[parentId]? with
  | none => exact .refl state
  | some parent =>
      simp only [parentFound]
      cases parentAllowed : destinationCanWrite state parentId with
      | false => exact .refl state
      | true =>
          simp only [parentAllowed]
          cases sourceFound : state.destinations[sourceId]? with
          | none => exact .refl state
          | some source =>
              simp only [sourceFound]
              cases sourceAllowed : destinationCanWrite state sourceId with
              | false => exact .refl state
              | true =>
                  simp only [sourceAllowed]
                  have inside := (Array.getElem?_eq_some_iff.mp sourceFound).choose
                  cases parentProgress : parent.progress <;> (try simp only [parentProgress]) <;> try exact .refl state
                  case «open» parentCount =>
                    cases progress : source.progress <;> (try simp only [progress]) <;> try exact .refl state
                    case built count =>
                      cases use : source.use <;> (try simp only [use]) <;> try exact .refl state
                      case receiver =>
                        cases backing : source.backing <;> (try simp only [backing]) <;> try exact .refl state
                        case direct storageId =>
                          have bound : storageId < state.storage.size := by
                            simpa only [backing, DestinationBacking.receiverStorage] using (valid.2.2.1 sourceId source sourceFound).2
                          have committed : ∀ storage : ReceivingStorage,
                              ForwardFrame state { state with storage := state.storage.set! storageId storage, destinations := state.destinations.set! sourceId { source with progress := .retired } } := by
                            intro storage
                            refine forward_leaf state sourceId source _ sourceFound ?_ ?_ ?_ ?_
                            · rfl
                            · simp [OwnershipLinkBacking, use]
                            · simp [progress, ReservationStableProgress]
                            · trivial
                          simp only [backing, use] at committed
                          cases stored : state.storage[storageId]?
                          all_goals repeat' first
                            | simp only [lookupStorage_result, stored, replaceStorage_result,
                                replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                                ConstructionM.get, ConstructionM.fail, emit_result, ConstructionResult.finalState]
                            | attach_split_if
                            | exact .refl state
                            | exact committed _



private theorem abandonRowsState_ownership_frame (rows : List PendingDestination) (state : ConstructionState)
    (current : ∀ row ∈ rows, state.destinations[row.capability.id]? = some row)
    (unique : rows.Pairwise fun first second => first.capability.id ≠ second.capability.id) :
    ReservationMetadataFrame state (abandonRowsState rows state) ∧
      ForwardFrame state (abandonRowsState rows state) := by
  induction rows generalizing state with
  | nil => exact ⟨.refl state, .refl state⟩
  | cons row rest ih =>
      let next : ConstructionState := { state with
        destinations := state.destinations.set! row.capability.id { row with progress := .abandoned }
        events := state.events ++ [.abandon row.capability.id] }
      have present := current row (List.mem_cons_self ..)
      have firstMetadata : ReservationMetadataFrame state next := by
        apply reservationMetadataFrame_replace_terminal state row.capability.id row _ state.storage _ present (Nat.le_refl _)
        · trivial
        · intro count selected; simp
        · intro index different
          simp [destinationObservations, observeDestination, Ne.symm different]
      have first : ForwardFrame state next := by
        refine forward_terminal state row.capability.id row _ present rfl ?_ ?_ rfl (Or.inr (Or.inl rfl))
        · cases use : row.use <;> simp [OwnershipLinkBacking, use]
        · trivial
      have remaining := ih next (by
        intro after member
        have different := (List.pairwise_cons.mp unique).1 after member
        simpa only [next, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different]
          using current after (List.mem_cons_of_mem _ member)) (List.pairwise_cons.mp unique).2
      simpa only [abandonRowsState, next] using And.intro (firstMetadata.trans remaining.1)
        (ForwardFrame.trans firstMetadata remaining.1 first remaining.2)

private theorem abandonPreservingExit_ownership_frame (id replacement : DestinationId) (state : ConstructionState)
    (indexed : DestinationCapabilitiesIndexed state) :
    ForwardFrame state (abandonPreservingExit id replacement state).finalState := by
  cases checked : protectedExitDiscarded state id replacement with
  | error fault =>
      simp only [abandonPreservingExit, ConstructionM.get, bind, checked, ConstructionM.fail,
        ConstructionResult.finalState]
      exact .refl state
  | ok rows =>
      rw [abandonPreservingExit_exact state id replacement indexed ⟨rows, checked⟩]
      apply (abandonRowsState_ownership_frame (protectedRows state id replacement) state ?_
        (protectedRows_indexed state id replacement indexed).2).2
      intro row member
      have original := (protectedRows_exact_selection state id replacement row).mp member
      obtain ⟨index, found⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp original.1)
      simpa only [indexed index row found] using found


local syntax "relocation_split_if" : tactic
elab_rules : tactic
  | `(tactic| relocation_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no relocation condition to split"
      return [yes.mvarId, no.mvarId]

local syntax "relocation_split_match" : tactic
elab_rules : tactic
  | `(tactic| relocation_split_match) => Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
      let target ← Lean.instantiateMVars (← goal.getType)
      let mut excluded : Lean.ExprSet := {}
      repeat
        let some expression ← Lean.Meta.findSplit? target .match excluded
          | Lean.throwError "no concrete relocation match to split"
        let some application ← Lean.Meta.matchMatcherApp? expression
          | Lean.throwError "expected relocation match"
        let abstractState ← application.discrs.anyM fun discriminant => do
          let type ← Lean.Meta.whnf (← Lean.Meta.inferType discriminant)
          return type.getAppFn.isConstOf ``ConstructionResult
        if abstractState then
          excluded := excluded.insert expression
        else
          try
            let some discriminant ← application.discrs.findM? (fun value => return !(← Lean.Meta.isConstructorApp value))
              | Lean.throwError "relocation match is already concrete"
            let (variables, generalized) ← goal.generalize #[{ expr := discriminant, hName? := some `relocationCase }]
            return (← generalized.cases variables[0]!).toList.map (·.mvarId)
          catch _ =>
            excluded := excluded.insert expression

private theorem fit_commit_lifecycle (state : ConstructionState) (id : DestinationId)
    (destination : PendingDestination) (count receiver stage start finish rollback : Nat)
    (storage : Array ReceivingStorage) (size : storage.size = state.storage.size)
    (present : state.destinations[id]? = some destination)
    (progress : destination.progress = .built count)
    (backing : destination.backing = .staged receiver stage)
    (receiving : destination.use = .receiver ∨ ∃ parent, destination.use = .child parent)
    (valid : DestinationLifecycleInvariant state) :
    ForwardFrame state { state with
      storage := storage
      destinations := state.destinations.set! id { destination with
        backing := .direct receiver
        capability := { destination.capability with start := start }
        writeEnd := finish
        rollbackEnd := rollback }
      events := state.events ++ [.copy (.storage stage []) id] } := by
  refine forward_leaf state id destination _ present ?_ ?_ ?_ ?_
  · rfl
  · cases use : destination.use <;> simp_all [OwnershipLinkBacking, DestinationBacking.receiverStorage]
  · simp [ReservationStableProgress, progress]
  · simp [OwnershipLeafProgress, progress]

set_option maxHeartbeats 2000000 in
private theorem fitStagedDestination_ownership_frame (id : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ForwardFrame state (fitStagedDestination id state).finalState := by
  simp only [fitStagedDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          cases progress : destination.progress <;> try simp only [progress] <;> try exact .refl state
          case built count =>
            cases backing : destination.backing <;> try simp only [backing] <;> try exact .refl state
            case staged receiver stage =>
              have receiverInside : receiver < state.storage.size := by
                simpa only [backing, DestinationBacking.receiverStorage] using (valid.2.2.1 id destination present).2
              have stageInside : stage < state.storage.size := by
                simpa only [PendingDestination.storage, backing, DestinationBacking.writeStorage] using
                  (valid.2.2.1 id destination present).1
              cases receiverResult : state.storage[receiver]?
              all_goals cases stageResult : state.storage[stage]?
              all_goals cases use : destination.use
              all_goals cases layout : destination.layout
              all_goals repeat' first
                | exact .refl state
                | solve
                  | simp only [← layout, ← use, ← backing, ← progress]
                    apply fit_commit_lifecycle state id destination count receiver stage _ _ _ _ _ present progress backing
                    · first | exact Or.inl use | exact Or.inr ⟨_, use⟩
                    · exact valid
                    · simp [Array.set!_eq_setIfInBounds]
                | simp only [lookupStorage_result, writableDestination_result,
                    ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                    replaceDestination_result, replaceStorage_result, emit_result,
                    inside, receiverInside, stageInside, receiverResult, stageResult, use, layout,
                    Array.size_set!, ↓reduceIte, bind, pure, ConstructionResult.finalState]
                | relocation_split_match
                | relocation_split_if



private abbrev publicationStep (id : DestinationId) : ConstructionM Unit :=
  (fun {left right : ConstructionM Unit} (_ : left = right) => left) (publishReady_transition id)

private theorem publish_commit_lifecycle (state : ConstructionState) (id : DestinationId)
    (destination : PendingDestination) (count start writeEnd : Nat) (stage : Option StorageId)
    (storage : Array ReceivingStorage) (size : storage.size = state.storage.size)
    (present : state.destinations[id]? = some destination)
    (progress : destination.progress = .built count)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant { state with
      storage := storage
      destinations := state.destinations.set! id { destination with
        progress := .published count
        backing := .direct destination.backing.receiverStorage
        capability := { destination.capability with start := start }
        writeEnd := writeEnd }
      events := state.events ++ (match stage with
        | none => [.publish id]
        | some stage => [.copy (.storage stage []) id, .publish id]) } := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply destinationTraceProtocol_replace state id destination _ _ present
      (by
        intro index different
        cases stage <;> simp [destinationObservations, observeDestination, Ne.symm different])
      _ valid.1
    intro phase matched
    cases phase <;> cases stage <;>
      simp_all [DestinationTracePhase.matchesDestination, DestinationTracePhase.matchesProgress,
        runDestinationTrace, destinationObservations, observeDestination,
        runDestinationObservations, destinationTraceStep]
  · exact destinationCapabilities_replace state id _ (valid.2.1 id destination present) valid.2.1
  · apply destinationStorageReferences_replace state id _ storage
    · omega
    · simpa only [size, PendingDestination.storage, DestinationBacking.writeStorage] using
        (valid.2.2.1 id destination present).2
    · simpa only [size, DestinationBacking.receiverStorage] using
        (valid.2.2.1 id destination present).2
    · exact valid.2.2.1
  · exact destinationOwnersOrdered_replace state id destination _ present rfl valid.2.2.2

set_option maxHeartbeats 2000000 in
private theorem publicationStep_preserves (id : DestinationId) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (publicationStep id state).finalState := by
  simp only [publicationStep, publishReady_transition, lookupDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact valid
  | some destination =>
      simp only [present]
      have inside := (Array.getElem?_eq_some_iff.mp present).choose
      cases progress : destination.progress <;> try simp only [progress] <;> try exact valid
      case built count =>
        cases use : destination.use <;> try simp only [use] <;> try exact valid
        case receiver =>
          cases backing : destination.backing with
          | direct receiver =>
              have receiverInside : receiver < state.storage.size := by
                simpa only [backing, DestinationBacking.receiverStorage] using
                  (valid.2.2.1 id destination present).2
              have committed := fun (start writeEnd : Nat) (storage : Array ReceivingStorage)
                  (size : storage.size = state.storage.size) =>
                publish_commit_lifecycle state id destination count start writeEnd none storage size
                  present progress valid
              simp only [backing, DestinationBacking.receiverStorage, use] at committed
              cases receiverResult : state.storage[receiver]?
              all_goals cases layout : destination.layout
              all_goals
                simp only [layout] at committed
                repeat' first
                  | simp only [backing, use, progress, layout, DestinationBacking.receiverStorage,
                      lookupStorage_result, receiverResult, replaceStorage_result, replaceDestination_result,
                      emit_result, receiverInside, inside, Array.size_set!, ↓reduceIte, bind, pure,
                      ConstructionM.fail, ConstructionResult.finalState, List.append_assoc]
                  | exact valid
                  | exact committed _ _ _ (by simp)
          | staged receiver stage =>
              have receiverInside : receiver < state.storage.size := by
                simpa only [backing, DestinationBacking.receiverStorage] using
                  (valid.2.2.1 id destination present).2
              have stageInside : stage < state.storage.size := by
                simpa only [PendingDestination.storage, backing, DestinationBacking.writeStorage] using
                  (valid.2.2.1 id destination present).1
              have committed := fun (start writeEnd : Nat) (storage : Array ReceivingStorage)
                  (size : storage.size = state.storage.size) =>
                publish_commit_lifecycle state id destination count start writeEnd (some stage) storage size
                  present progress valid
              simp only [backing, DestinationBacking.receiverStorage, use] at committed
              cases receiverResult : state.storage[receiver]?
              all_goals cases stageResult : state.storage[stage]?
              all_goals cases layout : destination.layout
              all_goals
                simp only [layout] at committed
                repeat' first
                  | simp only [backing, use, progress, layout, DestinationBacking.receiverStorage,
                      lookupStorage_result, receiverResult, stageResult, replaceStorage_result,
                      replaceDestination_result, emit_result, receiverInside, stageInside, inside,
                      Array.size_set!, ↓reduceIte, bind, pure, ConstructionM.fail,
                      ConstructionResult.finalState, List.append_assoc]
                  | exact valid
                  | exact committed _ _ _ (by simp)

private theorem publish_commit_metadata (state : ConstructionState) (id : DestinationId)
    (destination : PendingDestination) (count start writeEnd : Nat) (stage : Option StorageId)
    (storage : Array ReceivingStorage) (size : storage.size = state.storage.size)
    (present : state.destinations[id]? = some destination)
    (progress : destination.progress = .built count)
    (use : destination.use = .receiver) (valid : DestinationLifecycleInvariant state) :
    (ReservationMetadataFrame state { state with
      storage := storage
      destinations := state.destinations.set! id { destination with
        progress := .published count
        backing := .direct destination.backing.receiverStorage
        capability := { destination.capability with start := start }
        writeEnd := writeEnd }
      events := state.events ++ (match stage with
        | none => [.publish id]
        | some stage => [.copy (.storage stage []) id, .publish id]) }) ∧
    (ForwardFrame state { state with
      storage := storage
      destinations := state.destinations.set! id { destination with
        progress := .published count
        backing := .direct destination.backing.receiverStorage
        capability := { destination.capability with start := start }
        writeEnd := writeEnd }
      events := state.events ++ (match stage with
        | none => [.publish id]
        | some stage => [.copy (.storage stage []) id, .publish id]) }) := by
  constructor
  · apply reservationMetadataFrame_replace_mutable state id destination _ storage _ present
    · exact Nat.le_of_eq size.symm
    · simp [progress, ReservationStableProgress]
    · intro queried different
      cases stage <;> simp [destinationObservations, observeDestination, Ne.symm different]
  · refine forward_leaf state id destination _ present ?_ ?_ ?_ ?_
    · rfl
    · simp [OwnershipLinkBacking, use, DestinationBacking.receiverStorage]
    · simp [ReservationStableProgress, progress]
    · trivial

set_option maxHeartbeats 2000000 in
private theorem publicationStep_metadata (id : DestinationId) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state) :
    ReservationMetadataFrame state (publicationStep id state).finalState ∧
      ForwardFrame state (publicationStep id state).finalState := by
  simp only [publicationStep, publishReady_transition, lookupDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact ⟨.refl state, .refl state⟩
  | some destination =>
      simp only [present]
      have inside := (Array.getElem?_eq_some_iff.mp present).choose
      cases progress : destination.progress <;> try simp only [progress] <;> try exact ⟨.refl state, .refl state⟩
      case built count =>
        cases use : destination.use <;> try simp only [use] <;> try exact ⟨.refl state, .refl state⟩
        case receiver =>
          cases backing : destination.backing with
          | direct receiver =>
              have receiverInside : receiver < state.storage.size := by
                simpa only [backing, DestinationBacking.receiverStorage] using
                  (valid.2.2.1 id destination present).2
              have committed := fun (start writeEnd : Nat) (storage : Array ReceivingStorage)
                  (size : storage.size = state.storage.size) =>
                publish_commit_metadata state id destination count start writeEnd none storage size
                  present progress use valid
              simp only [backing, DestinationBacking.receiverStorage, use] at committed
              cases receiverResult : state.storage[receiver]?
              all_goals cases layout : destination.layout
              all_goals
                simp only [layout] at committed
                repeat' first
                  | simp only [backing, use, progress, layout, DestinationBacking.receiverStorage,
                      lookupStorage_result, receiverResult, replaceStorage_result, replaceDestination_result,
                      emit_result, receiverInside, inside, Array.size_set!, ↓reduceIte, bind, pure,
                      ConstructionM.fail, ConstructionResult.finalState, List.append_assoc]
                  | exact ⟨.refl state, .refl state⟩
                  | exact committed _ _ _ (by simp)
          | staged receiver stage =>
              have receiverInside : receiver < state.storage.size := by
                simpa only [backing, DestinationBacking.receiverStorage] using
                  (valid.2.2.1 id destination present).2
              have stageInside : stage < state.storage.size := by
                simpa only [PendingDestination.storage, backing, DestinationBacking.writeStorage] using
                  (valid.2.2.1 id destination present).1
              have committed := fun (start writeEnd : Nat) (storage : Array ReceivingStorage)
                  (size : storage.size = state.storage.size) =>
                publish_commit_metadata state id destination count start writeEnd (some stage) storage size
                  present progress use valid
              simp only [backing, DestinationBacking.receiverStorage, use] at committed
              cases receiverResult : state.storage[receiver]?
              all_goals cases stageResult : state.storage[stage]?
              all_goals cases layout : destination.layout
              all_goals
                simp only [layout] at committed
                repeat' first
                  | simp only [backing, use, progress, layout, DestinationBacking.receiverStorage,
                      lookupStorage_result, receiverResult, stageResult, replaceStorage_result,
                      replaceDestination_result, emit_result, receiverInside, stageInside, inside,
                      Array.size_set!, ↓reduceIte, bind, pure, ConstructionM.fail,
                      ConstructionResult.finalState, List.append_assoc]
                  | exact ⟨.refl state, .refl state⟩
                  | exact committed _ _ _ (by simp)

private theorem publicationLoop_preserves (ids : List DestinationId) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant
      (((do for id in ids do publicationStep id) : ConstructionM Unit) state).finalState ∧
      ReservationMetadataFrame state (((do for id in ids do publicationStep id) : ConstructionM Unit) state).finalState ∧
      ForwardFrame state (((do for id in ids do publicationStep id) : ConstructionM Unit) state).finalState := by
  induction ids generalizing state with
  | nil => exact ⟨valid, .refl state, .refl state⟩
  | cons id ids ih =>
      have preserved := And.intro (publicationStep_preserves id state valid) (publicationStep_metadata id state valid)
      cases result : publicationStep id state with
      | ok value after =>
          rw [result] at preserved
          have remaining := ih after preserved.1
          simpa only [List.forIn_cons, bind, pure, result, ConstructionResult.finalState] using
            And.intro remaining.1 (And.intro (preserved.2.1.trans remaining.2.1)
              (ForwardFrame.trans preserved.2.1 remaining.2.1 preserved.2.2 remaining.2.2))
      | fault kind after =>
          rw [result] at preserved
          simpa only [List.forIn_cons, bind, pure, result, ConstructionResult.finalState] using preserved

private theorem publishOperation_ownership_frame (ids : List DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ForwardFrame state (publishOperation ids state).finalState := by
  simp only [publishOperation, ConstructionM.get, bind]
  cases checked : preflightPublication state ids with
  | error fault => exact .refl state
  | ok value =>
      cases value
      change ForwardFrame state
        (((do for id in ids do publicationStep id) : ConstructionM Unit) state).finalState
      exact (publicationLoop_preserves ids state valid).2.2


private def TreeOwnershipRows (before after : ConstructionState) : Prop :=
  OwnershipChildSourceExtension before after ∧
    (∀ (id : DestinationId) (row : PendingDestination), before.destinations[id]? = some row →
      ∀ count selected, row.progress = .exiting count selected → after.destinations[id]? = some row) ∧
    (SupportedReplacementAuthorityRows before.destinations → SupportedReplacementAuthorityRows after.destinations) ∧
    InactiveBackingExtension before after ∧ (∀ id,
      ReplacementSupported {ConstructionState.initial with destinations := after.destinations} id →
      ReplacementSupported {ConstructionState.initial with destinations := before.destinations} id)

private theorem TreeOwnershipRows.refl (state : ConstructionState) : TreeOwnershipRows state state :=
  ⟨ownershipChildSourceExtension_refl state, (fun _ _ present _ _ _ => present), id,
    inactiveBackingExtension_refl state, fun _ supported => supported⟩

private theorem TreeOwnershipRows.trans {before middle after : ConstructionState}
    (first : TreeOwnershipRows before middle) (second : TreeOwnershipRows middle after) :
    TreeOwnershipRows before after :=
  ⟨ownershipChildSourceExtension_trans before middle after first.1 second.1,
    fun id row present count selected exiting =>
      second.2.1 id row (first.2.1 id row present count selected exiting) count selected exiting,
    fun valid => second.2.2.1 (first.2.2.1 valid),
    inactiveBackingExtension_trans before middle after first.2.2.2.1 second.2.2.2.1,
    fun id supported => first.2.2.2.2 id (second.2.2.2.2 id supported)⟩

private theorem treeOwnershipRows_weaken {before after : ConstructionState}
    (frame : TreeOwnershipRows before after) : RowsFrame before after := by
  refine ⟨⟨frame.1, ?_, frame.2.2.1⟩, frame.2.2.2.1, fun id _ supported => frame.2.2.2.2 id supported⟩
  intro id initial final initialPresent finalPresent count selected initialExiting _ _ _
  exact Option.some.inj (finalPresent.symm.trans (frame.2.1 id initial initialPresent count selected initialExiting))

private theorem treeOwnershipRows_replace_mutable (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (sameUse : after.use = before.use) (backing : OwnershipLinkBacking before after)
    (mutable : ¬ ReservationStableProgress before.progress) :
    TreeOwnershipRows state {state with destinations := state.destinations.set! id after} := by
  have frame := rows_mutable state id before after present sameUse backing mutable
  refine ⟨frame.children, ?_, frame.1.2.2, frame.2.1, ?_⟩
  · intro index row found count selected exiting
    have different : id ≠ index := by
      intro same
      subst index
      have equal := Option.some.inj (present.symm.trans found)
      subst row
      exact mutable (by simp [ReservationStableProgress, exiting])
    simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different] using found
  · intro index supported
    apply replacementSupported_replace_back {ConstructionState.initial with destinations := state.destinations} id before after present (fun parent use => sameUse.symm.trans use) _ index supported
    intro _
    cases progress : before.progress <;> simp_all [ReservationStableProgress, activeProgress]

private theorem abandonDestination_treeOwnershipRows (state : ConstructionState) (id : DestinationId) :
    TreeOwnershipRows state (abandonDestination id state).finalState := by
  simp only [abandonDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some row =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).1
          cases progress : row.progress <;> try simp only [progress] <;> try exact .refl state
          all_goals
            simp only [lookupStorage_result, bind]
            cases stored : state.storage[row.storage]? with
            | none => exact .refl state
            | some storage =>
                have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
                simp only [stored, replaceStorage_result, replaceDestination_result,
                  storageInside, inside, ↓reduceIte, bind, pure, emit_result, ConstructionResult.finalState]
                refine treeOwnershipRows_replace_mutable state id row _ present ?_ ?_ ?_
                · rfl
                · cases use : row.use <;> simp [OwnershipLinkBacking, use]
                · simp [ReservationStableProgress, progress]

private theorem treeCleanupStep_ownershipRows (row : PendingDestination) (state : ConstructionState)
    (present : state.destinations[row.capability.id]? = some row) :
    TreeOwnershipRows state (treeCleanupStep row state).finalState := by
  rw [treeCleanupStep_current_equation row state present]
  cases writable : destinationCanWrite state row.capability.id with
  | false => exact .refl state
  | true =>
      simp only [↓reduceIte]
      cases progress : row.progress <;>
        try exact abandonDestination_treeOwnershipRows state row.capability.id
      case suspended count child =>
        exact TreeOwnershipRows.trans
          (treeOwnershipRows_replace_mutable state row.capability.id row
            { row with progress := .open count } present rfl
            (by cases use : row.use <;> simp [OwnershipLinkBacking, use])
            (by simp [ReservationStableProgress, progress]))
          (abandonDestination_treeOwnershipRows _ row.capability.id)

private theorem treeCleanupLoop_ownershipRows (rows : List PendingDestination) (state : ConstructionState)
    (current : ∀ row ∈ rows, state.destinations[row.capability.id]? = some row)
    (unique : rows.Pairwise fun first second => first.capability.id ≠ second.capability.id) :
    TreeOwnershipRows state (treeCleanupLoop rows state).finalState := by
  induction rows generalizing state with
  | nil => exact .refl state
  | cons row rest ih =>
      simp only [treeCleanupLoop, bind]
      have first := treeCleanupStep_ownershipRows row state (current row (List.mem_cons_self ..))
      cases result : treeCleanupStep row state with
      | fault kind after => simpa only [result, ConstructionResult.finalState] using first
      | ok value after =>
          cases value
          have exactState := treeCleanupStep_success state after row
            (current row (List.mem_cons_self ..)) result
          simp only [result, ConstructionResult.finalState] at first
          subst after
          have remaining := ih (treeAbandonRowState state row) (by
            intro next member
            have different := (List.pairwise_cons.mp unique).1 next member
            simpa only [treeAbandonRowState, Array.set!_eq_setIfInBounds,
              Array.getElem?_setIfInBounds_ne different] using current next (List.mem_cons_of_mem _ member))
            (List.pairwise_cons.mp unique).2
          exact TreeOwnershipRows.trans first remaining

private theorem abandonTree_ownership_frame (id : DestinationId) (state : ConstructionState)
    (indexed : DestinationCapabilitiesIndexed state) :
    ForwardFrame state (abandonTree id state).finalState := by
  constructor
  · apply treeOwnershipRows_weaken
    rw [abandonTree_cleanup_equation]
    cases present : state.destinations[id]? with
    | none => exact .refl state
    | some parent =>
        cases writable : destinationCanWrite state id with
        | false => exact .refl state
        | true =>
            simp only [↓reduceIte]
            cases progress : parent.progress <;> simp only [progress] <;> try exact .refl state
            all_goals
              by_cases exiting : treeHasExiting (treeRows state id) = true
              · simpa only [exiting, Bool.false_eq_true, ↓reduceIte, ConstructionResult.finalState] using TreeOwnershipRows.refl state
              · simpa only [exiting, Bool.false_eq_true, ↓reduceIte] using treeCleanupLoop_ownershipRows (treeRows state id) state
                  (treeRows_indexed state id indexed).1 (treeRows_indexed state id indexed).2
  · exact abandonTree_forwardLinks_all_outcomes state id indexed



private def AdaptationReady (state : ConstructionState) (id : DestinationId) : Prop :=
  ∀ row, state.destinations[id]? = some row → OwnershipLeafProgress row.progress

private def AdaptationAction (id : DestinationId) (action : ConstructionM α) : Prop :=
  ∀ state, AdaptationReady state id →
    ReservationMetadataFrame state (action state).finalState ∧
      ForwardFrame state (action state).finalState ∧ AdaptationReady (action state).finalState id

private theorem adaptationReady_replace (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (progress : after.progress = before.progress) (ready : AdaptationReady state id) :
    AdaptationReady { state with destinations := state.destinations.set! id after } id := by
  intro row found
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have equal : after = row := by
    simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt inside,
      Option.some.injEq] using found
  subst row
  simpa only [progress] using ready before present

private theorem adaptation_commit (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (storage : Array ReceivingStorage)
    (present : state.destinations[id]? = some before) (size : storage.size = state.storage.size)
    (sameUse : after.use = before.use) (sameBacking : after.backing = before.backing)
    (progress : after.progress = before.progress) (ready : AdaptationReady state id) :
    ReservationMetadataFrame state { state with storage := storage, destinations := state.destinations.set! id after } ∧
      ForwardFrame state { state with storage := storage, destinations := state.destinations.set! id after } ∧
      AdaptationReady { state with storage := storage, destinations := state.destinations.set! id after } id := by
  refine ⟨(reservationMetadataFrame_storage state storage (Nat.le_of_eq size.symm)).trans
    (reservationMetadataFrame_replace { state with storage := storage } id before after present progress), ?_, ?_⟩
  · refine forward_terminal state id before after present sameUse ?_ ?_ sameBacking (Or.inl progress)
    · cases use : before.use <;> simp [OwnershipLinkBacking, use, sameBacking]
    · simpa only [progress] using ready before present
  · exact adaptationReady_replace state id before after present progress ready

private theorem adaptation_pure (id : DestinationId) (value : α) : AdaptationAction id (pure value) :=
  fun state ready => ⟨.refl state, .refl state, ready⟩

private theorem adaptation_fail (id : DestinationId) (fault : ConstructionFault) :
    AdaptationAction id (ConstructionM.fail (α := α) fault) := fun state ready => ⟨.refl state, .refl state, ready⟩

private theorem adaptation_fault_bind (id : DestinationId) (fault : ConstructionFault) (next : α → ConstructionM β) :
    AdaptationAction id (ConstructionM.fail fault >>= next) := fun state ready => ⟨.refl state, .refl state, ready⟩

private theorem adaptation_get (id : DestinationId) : AdaptationAction id ConstructionM.get :=
  fun state ready => ⟨.refl state, .refl state, ready⟩

private theorem adaptation_storage (state : ConstructionState) (id : DestinationId)
    (storage : Array ReceivingStorage) (size : state.storage.size ≤ storage.size) (ready : AdaptationReady state id) :
    ReservationMetadataFrame state { state with storage := storage } ∧
      ForwardFrame state { state with storage := storage } ∧ AdaptationReady { state with storage := storage } id :=
  ⟨reservationMetadataFrame_storage state storage size, forward_same state _ rfl, ready⟩

private theorem adaptation_bind (id : DestinationId) (action : ConstructionM α) (next : α → ConstructionM β)
    (first : AdaptationAction id action) (remaining : ∀ value, AdaptationAction id (next value)) :
    AdaptationAction id (action >>= next) := by
  intro state ready
  have initial := first state ready
  cases result : action state with
  | fault fault final => simpa only [result, bind, ConstructionResult.finalState] using initial
  | ok value middle =>
      simp only [result, ConstructionResult.finalState] at initial
      have rest := remaining value middle initial.2.2
      simpa only [result, bind] using And.intro (initial.1.trans rest.1)
        (And.intro (ForwardFrame.trans initial.1 rest.1 initial.2.1 rest.2.1) rest.2.2)

private theorem adaptation_if (id : DestinationId) (condition : Prop) [Decidable condition]
    (yes no : ConstructionM α) (first : AdaptationAction id yes) (second : AdaptationAction id no) :
    AdaptationAction id (if condition then yes else no) := by
  by_cases selected : condition <;> simp only [selected, ↓reduceIte] <;> assumption

private theorem adaptation_final_update (query : ConstructionM PendingDestination)
    (update : PendingDestination → ConstructionM Unit) (id : DestinationId)
    (queryResult : ∀ state, query state = match state.destinations[id]? with
      | some destination => .ok destination state
      | none => .fault .destination state)
    (safe : ∀ state destination, state.destinations[id]? = some destination →
      AdaptationReady state id → ReservationMetadataFrame state (update destination state).finalState ∧
        ForwardFrame state (update destination state).finalState ∧
        AdaptationReady (update destination state).finalState id) :
    AdaptationAction id (query >>= update) := by
  intro state ready
  simp only [bind, queryResult]
  cases present : state.destinations[id]? with
  | none => exact ⟨.refl state, .refl state, ready⟩
  | some destination => exact safe state destination present ready

local syntax "adaptation_split_if" : tactic
elab_rules : tactic
  | `(tactic| adaptation_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no ownership adaptation condition to split"
      return [yes.mvarId, no.mvarId]

private theorem removeConstructionHeader_ready (id : DestinationId)
    (state : ConstructionState) (ready : AdaptationReady state id) :
    AdaptationReady (removeConstructionHeader id state).finalState id := by
  simp only [removeConstructionHeader, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact ready
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact ready
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          cases progress : destination.progress <;> (try simp only [progress]) <;> try exact ready
          case built count =>
            have removed : ∀ storage : ReceivingStorage,
                AdaptationReady { state with
                  storage := state.storage.set! destination.storage storage
                  destinations := state.destinations.set! id { destination with layout := .elements, writeEnd := destination.writeEnd - 4 },
                  events := state.events ++ [.relocate id .headerRemoval] } id := by
              intro storage
              exact adaptationReady_replace state id destination _ present rfl ready
            simp only [progress] at removed
            cases stored : state.storage[destination.storage]? with
            | none =>
                repeat' first
                  | simp only [lookupStorage_result, stored, bind, ConstructionM.fail,
                      ConstructionResult.finalState]
                  | adaptation_split_if
                  | exact ready
            | some receiving =>
              have bound := (Array.getElem?_eq_some_iff.mp stored).choose
              repeat' first
                | simp only [lookupStorage_result, stored, replaceStorage_result,
                    replaceDestination_result, inside, bound, ↓reduceIte, pure, bind,
                    ConstructionM.fail, emit_result, ConstructionResult.finalState]
                | adaptation_split_if
                | exact ready
                | exact removed _

private theorem adaptation_removeHeader (id : DestinationId) : AdaptationAction id (removeConstructionHeader id) := by
  intro state ready
  exact ⟨removeConstructionHeader_metadata_frame id state,
    ⟨removeConstructionHeader_ownership_rows id state, removeConstructionHeader_forwardLinks id state⟩,
    removeConstructionHeader_ready id state ready⟩

set_option maxHeartbeats 2000000 in
private theorem finishConstructionAdaptation_ready (id : DestinationId) :
    AdaptationAction id (finishConstructionAdaptation id) := by
  unfold finishConstructionAdaptation
  repeat' first
    | with_reducible exact adaptation_pure id _
    | with_reducible exact adaptation_fail id _
    | with_reducible exact adaptation_fault_bind id _ _
    | with_reducible exact adaptation_get id
    | with_reducible exact adaptation_removeHeader _
    | solve
      | with_reducible apply adaptation_final_update _ _ id
        · intro state
          exact lookupDestination_result id state
        · intro state current present ready
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          simp only [replaceDestination_result, inside, ↓reduceIte, ConstructionResult.finalState]
          exact adaptation_commit state id current _ state.storage present rfl rfl rfl rfl ready
    | solve
      | intro state ready
        simp only [lookupDestination_result, lookupStorage_result, writableDestination_result,
          replaceStorage_result]
        repeat' first
          | exact ⟨.refl state, .refl state, ready⟩
          | solve
            | apply adaptation_storage state id _ _ ready
              simp [Array.set!_eq_setIfInBounds]
          | split
    | with_reducible apply adaptation_bind id
    | with_reducible apply adaptation_if id
    | dsimp only
    | split
    | intro value

set_option maxHeartbeats 2000000 in
private theorem normalizeProducerDestination_ready (id : DestinationId) (producerType : Construct.Ty) :
    AdaptationAction id (normalizeProducerDestination id producerType) := by
  unfold normalizeProducerDestination
  repeat' first
    | with_reducible exact adaptation_pure id _
    | with_reducible exact adaptation_fail id _
    | with_reducible exact adaptation_fault_bind id _ _
    | with_reducible exact adaptation_get id
    | with_reducible exact adaptation_removeHeader _
    | solve
      | with_reducible apply adaptation_final_update _ _ id
        · intro state
          exact lookupDestination_result id state
        · intro state current present ready
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          simp only [replaceDestination_result, inside, ↓reduceIte, ConstructionResult.finalState]
          exact adaptation_commit state id current _ state.storage present rfl rfl rfl rfl ready
    | solve
      | intro state ready
        simp only [lookupDestination_result, lookupStorage_result, writableDestination_result,
          replaceStorage_result]
        repeat' first
          | exact ⟨.refl state, .refl state, ready⟩
          | solve
            | apply adaptation_storage state id _ _ ready
              simp [Array.set!_eq_setIfInBounds]
          | split
    | with_reducible apply adaptation_bind id
    | with_reducible apply adaptation_if id
    | dsimp only
    | split
    | intro value

private theorem adaptationReady_of_leaf (state : ConstructionState) (id : DestinationId)
    (row : PendingDestination) (present : state.destinations[id]? = some row)
    (leaf : OwnershipLeafProgress row.progress) : AdaptationReady state id := by
  intro current found
  have equal := Option.some.inj (present.symm.trans found)
  subst current
  exact leaf

private theorem finishConstructionAdaptation_ownership_frame (id : DestinationId)
    (state : ConstructionState) : ForwardFrame state (finishConstructionAdaptation id state).finalState := by
  by_cases ready : AdaptationReady state id
  · exact (finishConstructionAdaptation_ready id state ready).2.1
  · cases present : state.destinations[id]? with
    | none =>
        apply False.elim
        apply ready
        intro current found
        simp only [present] at found
        contradiction
    | some row =>
        by_cases leaf : OwnershipLeafProgress row.progress
        · exact False.elim (ready (adaptationReady_of_leaf state id row present leaf))
        · cases progress : row.progress <;> simp [progress, OwnershipLeafProgress] at leaf
          all_goals
            cases allowed : destinationCanWrite state id
            all_goals cases adaptation : row.adaptation <;>
              simp only [finishConstructionAdaptation, lookupDestination_result, writableDestination_result, present, allowed, adaptation, progress,
                bind, pure, ConstructionM.fail, ConstructionResult.finalState]
            all_goals exact .refl state

private theorem normalizeProducerDestination_ownership_frame (id : DestinationId) (producerType : Construct.Ty)
    (state : ConstructionState) : ForwardFrame state (normalizeProducerDestination id producerType state).finalState := by
  by_cases ready : AdaptationReady state id
  · exact (normalizeProducerDestination_ready id producerType state ready).2.1
  · cases present : state.destinations[id]? with
    | none =>
        apply False.elim
        apply ready
        intro current found
        simp only [present] at found
        contradiction
    | some row =>
        by_cases leaf : OwnershipLeafProgress row.progress
        · exact False.elim (ready (adaptationReady_of_leaf state id row present leaf))
        · cases progress : row.progress <;> simp [progress, OwnershipLeafProgress] at leaf
          all_goals
            cases allowed : destinationCanWrite state id
            all_goals cases adaptation : row.adaptation <;>
              simp only [normalizeProducerDestination, lookupDestination_result, writableDestination_result, present, allowed, adaptation, progress,
                bind, pure, ConstructionM.fail, ConstructionResult.finalState]
            all_goals exact .refl state

set_option maxHeartbeats 1000000 in
private theorem adaptConstructionDestination_ownership_frame (id : DestinationId)
    (producerType : Construct.Ty) (request : ConstructionRequest)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    ForwardFrame state (adaptConstructionDestination id producerType request state).finalState := by
  simp only [adaptConstructionDestination, writableDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact .refl state
  | some destination =>
      simp only [present]
      cases allowed : destinationCanWrite state id with
      | false => exact .refl state
      | true =>
          simp only [allowed]
          have inside := (Array.getElem?_eq_some_iff.mp present).choose
          have storageInside := (valid.2.2.1 id destination present).1
          cases progress : destination.progress <;> try simp only [progress] <;> try exact .refl state
          case «open» count =>
            cases count with
            | succ count => exact .refl state
            | zero =>
                cases stored : state.storage[destination.storage]?
                all_goals repeat' first
                  | exact .refl state
                  | solve
                    | refine forward_leaf state id destination _ present ?_ ?_ ?_ ?_
                      · rfl
                      · cases use : destination.use <;> simp [OwnershipLinkBacking, use]
                      · simp [ReservationStableProgress, progress]
                      · trivial
                  | simp only [ConstructionM.get, ConstructionM.set, ConstructionM.fail,
                      lookupStorage_result, replaceDestination_result, replaceStorage_result,
                      inside, storageInside, stored, ↓reduceIte, bind, pure, ConstructionResult.finalState]
                  | adaptation_split_if
                  | split



end InactiveProof
private theorem unchanged_inactive_support (before after : ConstructionState)
    (same : after.destinations = before.destinations) :
    InactiveBackingExtension before after ∧ ReplacementSupportExtension before after :=
  ⟨InactiveProof.inactive_same_rows before after same,
    fun id _ supported => replacementSupported_congr_destinations after before same.symm id supported⟩

theorem constructionPrimitive_inactive_support {α : Type} (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state) :
    InactiveBackingExtension state (action state).finalState ∧
      ReplacementSupportExtension state (action state).finalState := by
  have rows {after : ConstructionState} (frame : InactiveProof.RowsFrame state after) :
      InactiveBackingExtension state after ∧ ReplacementSupportExtension state after := ⟨frame.2.1, InactiveProof.support_actual state after frame.2.2⟩
  have forward {after : ConstructionState} (frame : InactiveProof.ForwardFrame state after) :
      InactiveBackingExtension state after ∧ ReplacementSupportExtension state after := ⟨frame.1.2.1, InactiveProof.support_actual state after frame.1.2.2⟩
  cases primitive with
  | reserveStorage bytes count => exact unchanged_inactive_support state _ rfl
  | appendStdout bytes => exact unchanged_inactive_support state _ rfl
  | adaptDestinationType id ty => exact rows (InactiveProof.adaptDestinationType_ownership_rows state id ty)
  | restoreReceivingLayout id layout => exact rows (InactiveProof.restoreReceivingLayout_ownership_rows state id layout)
  | removeConstructionHeader id => exact rows (InactiveProof.removeConstructionHeader_ownership_rows id state)
  | landExitReplacement id => exact landExitReplacement_inactive_support id state valid
  | abandonPreservingExit id replacement => exact forward (InactiveProof.abandonPreservingExit_ownership_frame id replacement state valid.2.1)
  | recordCopy source id => exact unchanged_inactive_support state _ (recordCopy_keepsOwnershipTable source id state)
  | writeElement id bytes => exact rows (InactiveProof.writeElement_ownership_rows id bytes state valid)
  | finishDestination id => exact rows (InactiveProof.finishDestination_ownership_rows state id valid)
  | attachChild parent child => exact forward (InactiveProof.attachChild_ownership_frame parent child state valid)
  | attachExtension parent child => exact forward (InactiveProof.attachExtension_ownership_frame parent child state valid)
  | attachElementExtension parent child => exact forward (InactiveProof.attachElementExtension_ownership_frame parent child state valid)
  | publishElementDestination id => exact forward (InactiveProof.publishElementDestination_ownership_frame id state valid)
  | retireRepeatedSource parent source => exact forward (InactiveProof.retireRepeatedSource_ownership_frame parent source state valid)
  | truncateConstructionStorage storage start finish count owner retain =>
      exact rows (InactiveProof.truncateConstructionStorage_ownership_rows storage start finish count owner retain state valid)
  | prepareNamedBinding id ty => exact rows (InactiveProof.prepareNamedBinding_ownership_rows id ty state valid)
  | fitStagedDestination id => exact forward (InactiveProof.fitStagedDestination_ownership_frame id state valid)
  | publishOperation ids => exact forward (InactiveProof.publishOperation_ownership_frame ids state valid)
  | abandonDestination id => exact rows (InactiveProof.abandonDestination_ownership_rows state id)
  | stageDestination id => exact rows (InactiveProof.stageDestination_ownership_rows state id)
  | abandonTree id => exact forward (InactiveProof.abandonTree_ownership_frame id state valid.2.1)
  | adaptConstructionDestination id ty request => exact forward (InactiveProof.adaptConstructionDestination_ownership_frame id ty request state valid)
  | finishConstructionAdaptation id => exact forward (InactiveProof.finishConstructionAdaptation_ownership_frame id state)
  | normalizeProducerDestination id ty => exact forward (InactiveProof.normalizeProducerDestination_ownership_frame id ty state)
  | openDestination storage capability layout known => exact rows (InactiveProof.openDestination_ownership_rows storage capability layout known state valid)
  | openDestinationDirect storage capability layout known => exact rows (InactiveProof.openDestinationDirect_ownership_rows storage capability layout known state valid)
  | openChild parent ty layout => exact rows (InactiveProof.openChild_ownership_rows parent ty layout state valid)
  | openExtension parent request known => exact rows (InactiveProof.openExtension_ownership_rows parent request known state valid)
  | openElementExtension parent ty layout known receiver => exact rows (InactiveProof.openElementExtension_ownership_rows parent ty layout known receiver state valid)
  | openExitReplacement parent => exact rows (InactiveProof.openExitReplacement_ownership_rows parent state valid)

theorem constructionPrimitive_inactiveBacking {α : Type} (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state) :
    InactiveBackingExtension state (action state).finalState :=
  (constructionPrimitive_inactive_support action primitive state valid).1

theorem constructionPrimitive_replacementSupportExtension {α : Type} (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state) :
    ReplacementSupportExtension state (action state).finalState :=
  (constructionPrimitive_inactive_support action primitive state valid).2

theorem constructionPrimitive_resumptionBackingSources {α : Type} (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state) (sources : ResumptionBackingSources state) :
    ResumptionBackingSources (action state).finalState :=
  resumptionBackingSources_extension state _ (constructionPrimitive_inactiveBacking action primitive state valid)
    (constructionPrimitive_reservation_frame action primitive state valid).resumptions sources

theorem constructionPrimitive_unsupportedResumptionKeys {α : Type} (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) (state : ConstructionState)
    (valid : DestinationLifecycleInvariant state) (sources : ResumptionBackingSources state)
    (unsupported : UnsupportedResumptionKeys state) : UnsupportedResumptionKeys (action state).finalState :=
  unsupportedResumptionKeys_extension state _ (constructionPrimitive_replacementSupportExtension action primitive state valid)
    (constructionPrimitive_reservation_frame action primitive state valid).resumptions sources unsupported

theorem resumptionBackingPrimitives : ConstructionProtocolPrimitives
    (fun state => ReservationLifecycleInvariant state ∧ ResumptionBackingSources state ∧ UnsupportedResumptionKeys state) where
  storageFrame := by
    intro state storage size valid
    have reservation := reservationLifecyclePrimitives.storageFrame state storage size valid.1
    have frame := unchanged_inactive_support state {state with storage := storage} rfl
    exact ⟨reservation, resumptionBackingSources_extension state _ frame.1 rfl valid.2.1,
      unsupportedResumptionKeys_extension state _ frame.2 rfl valid.2.1 valid.2.2⟩
  preserves := by
    intro α action primitive state valid
    exact ⟨reservationLifecyclePrimitives.preserves action primitive state valid.1,
      constructionPrimitive_resumptionBackingSources action primitive state valid.1.1 valid.2.1,
      constructionPrimitive_unsupportedResumptionKeys action primitive state valid.1.1 valid.2.1 valid.2.2⟩

end Goose.Proofs.ConstructionExecutionOwnership
