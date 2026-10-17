import Goose.Proofs.ConstructionExecutionOwnershipEvaluationReceiving
import Goose.Proofs.ConstructionExecutionOwnershipSourceState

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core Goose.Proofs.ConstructionExecutionProtocol

theorem OwnershipReplacementPath.sourcePreimage (before after : ConstructionState)
    (source : OwnershipSourceExtension before after) (ordered : DestinationOwnersOrdered after)
    (receiving node : DestinationId) (path : OwnershipReplacementPath after.destinations receiving node) :
    node < before.destinations.size → OwnershipReplacementPath before.destinations receiving node := by
  induction path with
  | refl => intro _; exact .refl _
  | step id parent ancestor row present use path previous =>
      intro inside
      let oldRow := before.destinations[id]
      have oldPresent : before.destinations[id]? = some oldRow := Array.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩
      obtain ⟨actual, actualPresent, sameUse, _⟩ := source id oldRow oldPresent
      have equal : actual = row := Option.some.inj (actualPresent.symm.trans present)
      subst actual
      have parentEarlier : parent < id := by simpa only [use] using ordered id row present
      exact .step id parent ancestor oldRow oldPresent (sameUse.symm.trans use)
        (previous (Nat.lt_trans parentEarlier inside))

theorem ownershipReceivingWithinSuccessorFrames_source (before after : ConstructionState)
    (outer : OwnershipAmbient) (receiving : DestinationId)
    (lifecycle : ReservationLifecycleInvariant before) (successors : DestinationSuccessorsValid before)
    (ordered : DestinationOwnersOrdered after) (source : OwnershipSourceExtension before after)
    (map : after.destinationSuccessors = before.destinationSuccessors)
    (tickets : ∀ (token : ExitReservationId) (incoming reserved : DestinationId) (snapshot : PendingDestination),
      after.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) →
      before.exitReservations[token]? = some (.active .fresh incoming reserved snapshot))
    (valid : OwnershipReceivingWithinSuccessorFrames before outer receiving) :
    OwnershipReceivingWithinSuccessorFrames after outer receiving := by
  intro frame member token owned incoming reserved snapshot node ticket aliases ancestry
  have oldTicket := tickets token incoming reserved snapshot ticket
  have oldAliases := aliases.congr map.symm
  have inside := oldAliases.bound successors (lifecycle.2.active token .fresh incoming reserved snapshot oldTicket).2.1
  exact valid frame member token owned incoming reserved snapshot node oldTicket oldAliases
    (ancestry.sourcePreimage before after source ordered receiving node inside)

theorem ownershipReceivingWithinSuccessorFrames_last (state : ConstructionState) (outer : OwnershipAmbient)
    (receiving : DestinationId) (lifecycle : ReservationLifecycleInvariant state)
    (successors : DestinationSuccessorsValid state) (last : state.destinations.size ≤ receiving + 1) :
    OwnershipReceivingWithinSuccessorFrames state outer receiving := by
  intro frame member token owned incoming reserved snapshot node ticket aliases ancestry
  have inside : node < state.destinations.size := aliases.bound successors (lifecycle.2.active token .fresh incoming reserved snapshot ticket).2.1
  have ordered : receiving ≤ node := OwnershipReplacementPath.le (state := state) lifecycle.1.2.2.2 ancestry
  exact Nat.le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le inside last)) ordered

def OwnershipChannelReceivingBound (state : ConstructionState) : Channel → Prop
  | .register _ => True
  | .construct incoming => incoming < state.destinations.size
  | .completion token => ∀ incoming,
      state.exitReservations[token]? = some (.waiting incoming) → incoming < state.destinations.size

theorem ownershipChannelReceivingWithinFrames_source (before after : ConstructionState)
    (outer : OwnershipAmbient) (channel : Channel)
    (lifecycle : ReservationLifecycleInvariant before) (successors : DestinationSuccessorsValid before)
    (ordered : DestinationOwnersOrdered after) (source : OwnershipSourceExtension before after)
    (map : after.destinationSuccessors = before.destinationSuccessors)
    (size : before.destinations.size ≤ after.destinations.size)
    (tickets : after.exitReservations = before.exitReservations)
    (bound : OwnershipChannelReceivingBound before channel)
    (valid : OwnershipChannelReceivingWithinFrames before outer channel) :
    OwnershipChannelReceivingWithinFrames after outer channel := by
  have transfer (incoming : DestinationId) (inside : incoming < before.destinations.size)
      (within : ∀ receiving, destinationCurrent before incoming = .ok receiving →
        OwnershipReceivingWithinSuccessorFrames before outer receiving) :
      ∀ receiving, destinationCurrent after incoming = .ok receiving →
        OwnershipReceivingWithinSuccessorFrames after outer receiving := by
    intro receiving resolved
    obtain ⟨oldCurrent, oldResolved, _⟩ := destinationCurrent_total before successors incoming inside
    have extended := destinationCurrent_extension before after map size incoming oldCurrent oldResolved
    have same : receiving = oldCurrent := Except.ok.inj (resolved.symm.trans extended)
    subst receiving
    apply ownershipReceivingWithinSuccessorFrames_source before after outer oldCurrent lifecycle successors
      ordered source map _ (within oldCurrent oldResolved)
    intro token incoming reserved snapshot present
    simpa only [tickets] using present
  cases channel with
  | register ty => trivial
  | construct incoming => exact transfer incoming bound valid
  | completion token =>
      constructor
      · intro incoming ticket
        have oldTicket : before.exitReservations[token]? = some (.waiting incoming) := by
          simpa only [tickets] using ticket
        exact transfer incoming (bound incoming oldTicket) (valid.1 incoming oldTicket)
      · intro role incoming selected snapshot ticket
        have oldTicket : before.exitReservations[token]? = some (.active role incoming selected snapshot) := by
          simpa only [tickets] using ticket
        exact transfer selected (lifecycle.2.active token role incoming selected snapshot oldTicket).2.1
          (valid.2 role incoming selected snapshot oldTicket)

theorem ownershipChannelReceivingBound_extension (before after : ConstructionState) (channel : Channel)
    (size : before.destinations.size ≤ after.destinations.size)
    (tickets : after.exitReservations = before.exitReservations) (valid : OwnershipChannelReceivingBound before channel) :
    OwnershipChannelReceivingBound after channel := by
  cases channel with
  | register ty => trivial
  | construct incoming => exact Nat.lt_of_lt_of_le valid size
  | completion token =>
      intro incoming ticket
      exact Nat.lt_of_lt_of_le (valid incoming (by simpa only [tickets] using ticket)) size

theorem constructionPrimitive_channelReceiving_of_sourceExtension {α : Type} (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) (state : ConstructionState) (valid : OwnershipSourceState state)
    (outer : OwnershipAmbient) (channel : Channel) (bound : OwnershipChannelReceivingBound state channel)
    (receiving : OwnershipChannelReceivingWithinFrames state outer channel)
    (source : OwnershipSourceExtension state (action state).finalState) :
    OwnershipChannelReceivingWithinFrames (action state).finalState outer channel ∧
      OwnershipChannelReceivingBound (action state).finalState channel := by
  have metadata := constructionPrimitive_reservation_frame action primitive state valid.structural.1.1.1
  have after := constructionPrimitive_sourceState_of_sourceExtension action primitive state valid source
  exact ⟨ownershipChannelReceivingWithinFrames_source state _ outer channel valid.structural.1.1
    valid.structural.2.1 after.structural.1.1.1.2.2.2 source
    (constructionPrimitive_successorMap action primitive state) metadata.destinations metadata.tickets bound receiving,
    ownershipChannelReceivingBound_extension state _ channel metadata.destinations metadata.tickets bound⟩

theorem constructionPrimitive_channelReceiving_or_landing {α : Type} (action : ConstructionM α)
    (primitive : ConstructionPrimitive action) (state : ConstructionState) (valid : OwnershipSourceState state)
    (outer : OwnershipAmbient) (channel : Channel) (bound : OwnershipChannelReceivingBound state channel)
    (receiving : OwnershipChannelReceivingWithinFrames state outer channel) :
    (OwnershipChannelReceivingWithinFrames (action state).finalState outer channel ∧
      OwnershipChannelReceivingBound (action state).finalState channel) ∨ ∃ id, HEq action (landExitReplacement id) := by
  rcases constructionPrimitive_source_or_landing action primitive state valid.structural.1.1.1 with source | landing
  · exact Or.inl (constructionPrimitive_channelReceiving_of_sourceExtension action primitive state valid
      outer channel bound receiving source)
  · exact Or.inr landing

end Goose.Proofs.ConstructionExecutionOwnership
