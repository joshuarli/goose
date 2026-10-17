import Goose.Proofs.ConstructionExecutionOwnershipLinks
import Goose.Construct.Runtime
import Goose.Proofs.ConstructionExecutionOwnershipReservations

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

def ResumptionSource (state : ConstructionState) (id : DestinationId)
    (snapshot : PendingDestination) : Prop :=
  ∃ current, state.destinations[id]? = some current ∧ activeProgress current.progress = false ∧
    current.use = snapshot.use ∧ OwnershipLinkBacking current snapshot

def ResumptionSources (state : ConstructionState) : Prop :=
  ∀ id snapshot, state.destinationResumptions.lookup id = some snapshot → ResumptionSource state id snapshot

def InactiveRowSourceExtension (before after : ConstructionState) : Prop :=
  ∀ (id : DestinationId) (row : PendingDestination), before.destinations[id]? = some row →
    activeProgress row.progress = false →
    ∃ current, after.destinations[id]? = some current ∧ activeProgress current.progress = false ∧
      current.use = row.use ∧ OwnershipLinkBacking row current

theorem resumptionSource_child_storage (state : ConstructionState)
    (links : DestinationForwardLinks state) (id parent count : Nat)
    (snapshot owner : PendingDestination) (source : ResumptionSource state id snapshot)
    (use : snapshot.use = .child parent) (present : state.destinations[parent]? = some owner)
    (suspended : owner.progress = .suspended count id) :
    snapshot.backing.receiverStorage = owner.storage := by
  obtain ⟨current, found, _, sameUse, backing⟩ := source
  have edge := links parent owner present
  simp only [DestinationForwardLink, suspended] at edge
  obtain ⟨selected, selectedPresent, _, selectedBacking⟩ := edge
  have equal : selected = current := Option.some.inj (selectedPresent.symm.trans found)
  subst selected
  simp only [OwnershipLinkBacking, sameUse, use] at backing
  exact backing.trans selectedBacking

theorem resumptionSource_replacement_backing (state : ConstructionState)
    (links : DestinationForwardLinks state) (id parent count : Nat)
    (snapshot owner : PendingDestination) (source : ResumptionSource state id snapshot)
    (use : snapshot.use = .replacement parent) (present : state.destinations[parent]? = some owner)
    (exiting : owner.progress = .exiting count id) : snapshot.backing = owner.backing := by
  obtain ⟨current, found, _, sameUse, backing⟩ := source
  have edge := links parent owner present
  simp only [DestinationForwardLink, exiting] at edge
  obtain ⟨selected, selectedPresent, _, selectedBacking⟩ := edge
  have equal : selected = current := Option.some.inj (selectedPresent.symm.trans found)
  subst selected
  simp only [OwnershipLinkBacking, sameUse, use] at backing
  exact backing.trans selectedBacking

theorem resumptionSource_extension (before after : ConstructionState)
    (extension : InactiveRowSourceExtension before after) (id : DestinationId)
    (snapshot : PendingDestination) (source : ResumptionSource before id snapshot) :
    ResumptionSource after id snapshot := by
  obtain ⟨row, present, inactive, use, backing⟩ := source
  obtain ⟨current, found, currentInactive, sameUse, currentBacking⟩ := extension id row present inactive
  refine ⟨current, found, currentInactive, sameUse.trans use, ?_⟩
  cases kind : row.use <;> simp only [OwnershipLinkBacking, kind, sameUse] at backing currentBacking ⊢
  all_goals exact backing.trans currentBacking.symm

theorem resumptionSources_extension (before after : ConstructionState)
    (extension : InactiveRowSourceExtension before after)
    (resumptions : after.destinationResumptions = before.destinationResumptions)
    (sources : ResumptionSources before) : ResumptionSources after := by
  intro id snapshot present
  rw [resumptions] at present
  exact resumptionSource_extension before after extension id snapshot (sources id snapshot present)

theorem inactiveRowSourceExtension_refl (state : ConstructionState) :
    InactiveRowSourceExtension state state := by
  intro id row present inactive
  exact ⟨row, present, inactive, rfl, by cases use : row.use <;> simp [OwnershipLinkBacking, use]⟩

theorem inactiveRowSourceExtension_trans (before middle after : ConstructionState)
    (first : InactiveRowSourceExtension before middle) (second : InactiveRowSourceExtension middle after) :
    InactiveRowSourceExtension before after := by
  intro id row present inactive
  obtain ⟨interim, found, interimInactive, use, backing⟩ := first id row present inactive
  obtain ⟨current, currentPresent, currentInactive, currentUse, currentBacking⟩ :=
    second id interim found interimInactive
  refine ⟨current, currentPresent, currentInactive, currentUse.trans use, ?_⟩
  cases kind : row.use <;> simp only [OwnershipLinkBacking, kind, use] at backing currentBacking ⊢
  all_goals exact currentBacking.trans backing

theorem resumptionSources_unchanged (before after : ConstructionState)
    (destinations : after.destinations = before.destinations)
    (resumptions : after.destinationResumptions = before.destinationResumptions)
    (sources : ResumptionSources before) : ResumptionSources after := by
  simpa only [ResumptionSources, ResumptionSource, destinations, resumptions] using sources

theorem waitExitDestination_resumptionSources (state : ConstructionState) (incoming : DestinationId)
    (sources : ResumptionSources state) : ResumptionSources (waitExitDestination incoming state).finalState := by
  simpa only [waitExitDestination, ConstructionM.get, ConstructionM.set, bind, pure,
    ConstructionResult.finalState, ResumptionSources, ResumptionSource] using sources

theorem releaseExitReservation_resumptionSources (state : ConstructionState) (token : ExitReservationId)
    (sources : ResumptionSources state) : ResumptionSources (releaseExitReservation token state).finalState := by
  have frame := releaseExitReservation_preserves_construction state token
  exact resumptionSources_unchanged state _ frame.2.1 frame.2.2.2.2.2.1 sources

theorem initial_resumptionSources : ResumptionSources .initial := by
  intro id snapshot present
  simp [ConstructionState.initial] at present

end Goose.Proofs.ConstructionExecutionOwnership
