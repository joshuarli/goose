import Goose.Proofs.ConstructionExecutionOwnershipLinkRowsMutations

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

def OwnershipForwardRowsFrame (before after : ConstructionState) : Prop :=
  OwnershipLinkRowsFrame before after ∧ (DestinationForwardLinks before → DestinationForwardLinks after)

theorem OwnershipForwardRowsFrame.refl (state : ConstructionState) : OwnershipForwardRowsFrame state state :=
  ⟨.refl state, id⟩

theorem OwnershipForwardRowsFrame.trans {before middle after : ConstructionState}
    (firstMetadata : ReservationMetadataFrame before middle) (secondMetadata : ReservationMetadataFrame middle after)
    (first : OwnershipForwardRowsFrame before middle) (second : OwnershipForwardRowsFrame middle after) :
    OwnershipForwardRowsFrame before after :=
  ⟨OwnershipLinkRowsFrame.trans firstMetadata secondMetadata first.1 second.1,
    fun valid => second.2 (first.2 valid)⟩

theorem ownershipForwardRowsFrame_same_rows (before after : ConstructionState)
    (same : after.destinations = before.destinations) : OwnershipForwardRowsFrame before after := by
  refine ⟨ownershipLinkRowsFrame_same_rows before after same, ?_⟩
  intro valid
  simpa only [DestinationForwardLinks, DestinationForwardLink, same] using valid

theorem ownershipForwardRowsFrame_replace_leaf (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (sameUse : after.use = before.use) (backing : OwnershipLinkBacking before after)
    (mutable : ¬ ReservationStableProgress before.progress) (leaf : OwnershipLeafProgress after.progress) :
    OwnershipForwardRowsFrame state { state with destinations := state.destinations.set! id after } := by
  refine ⟨ownershipLinkRowsFrame_replace_mutable state id before after present sameUse backing mutable, ?_⟩
  intro valid
  apply destinationForwardLinks_replace_sources state id before after present sameUse backing valid
  cases progress : after.progress <;> simp_all [OwnershipLeafProgress, DestinationForwardLink]

theorem ownershipForwardRowsFrame_replace_terminal (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (sameUse : after.use = before.use) (backing : OwnershipLinkBacking before after)
    (leaf : OwnershipLeafProgress after.progress)
    (sameBacking : after.backing = before.backing)
    (phase : after.progress = before.progress ∨ after.progress = .abandoned ∨ after.progress = .cancelled) :
    OwnershipForwardRowsFrame state { state with destinations := state.destinations.set! id after } := by
  refine ⟨ownershipLinkRowsFrame_replace_terminal state id before after present sameUse backing ?_ sameBacking phase, ?_⟩
  · intro count selected exiting
    simp only [exiting, OwnershipLeafProgress] at leaf
  · intro valid
    clear phase
    apply destinationForwardLinks_replace_sources state id before after present sameUse backing valid
    cases progress : after.progress <;> simp_all [OwnershipLeafProgress, DestinationForwardLink]

theorem ownershipForwardRowsFrame_two_leaf (state : ConstructionState) (first second : DestinationId)
    (beforeFirst beforeSecond afterFirst afterSecond : PendingDestination)
    (firstPresent : state.destinations[first]? = some beforeFirst)
    (secondPresent : state.destinations[second]? = some beforeSecond) (different : first ≠ second)
    (firstUse : afterFirst.use = beforeFirst.use) (secondUse : afterSecond.use = beforeSecond.use)
    (firstBacking : OwnershipLinkBacking beforeFirst afterFirst)
    (secondBacking : OwnershipLinkBacking beforeSecond afterSecond)
    (firstMutable : ¬ ReservationStableProgress beforeFirst.progress)
    (secondMutable : ¬ ReservationStableProgress beforeSecond.progress)
    (firstLeaf : OwnershipLeafProgress afterFirst.progress)
    (secondLeaf : OwnershipLeafProgress afterSecond.progress) :
    OwnershipForwardRowsFrame state { state with
      destinations := (state.destinations.set! first afterFirst).set! second afterSecond } := by
  refine ⟨ownershipLinkRowsFrame_two_mutable state first second beforeFirst beforeSecond afterFirst afterSecond
    firstPresent secondPresent different firstUse secondUse firstBacking secondBacking firstMutable secondMutable, ?_⟩
  intro valid
  let middle := { state with destinations := state.destinations.set! first afterFirst }
  have firstValid : DestinationForwardLinks middle := by
    apply destinationForwardLinks_replace_sources state first beforeFirst afterFirst firstPresent firstUse firstBacking valid
    cases progress : afterFirst.progress <;> simp_all [OwnershipLeafProgress, DestinationForwardLink]
  have secondPresent' : middle.destinations[second]? = some beforeSecond := by
    simpa only [middle, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different] using secondPresent
  apply destinationForwardLinks_replace_sources middle second beforeSecond afterSecond secondPresent'
    secondUse secondBacking firstValid
  cases progress : afterSecond.progress <;> simp_all [OwnershipLeafProgress, DestinationForwardLink]

end Goose.Proofs.ConstructionExecutionOwnership
