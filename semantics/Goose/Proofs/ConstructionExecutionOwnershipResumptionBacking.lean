import Goose.Proofs.ConstructionExecutionOwnershipResumptionSources
import Goose.Proofs.ConstructionExecutionOwnershipReplacementSupport

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Core

def SnapshotBackingAgrees (snapshot current : PendingDestination) : Prop :=
  match snapshot.use with
  | .receiver => True
  | .child _ => snapshot.backing.receiverStorage = current.backing.receiverStorage
  | .replacement _ => snapshot.backing = current.backing

def ResumptionBackingSource (state : ConstructionState) (id : DestinationId)
    (snapshot : PendingDestination) : Prop :=
  ∃ current, state.destinations[id]? = some current ∧ activeProgress current.progress = false ∧
    SnapshotBackingAgrees snapshot current

def ResumptionBackingSources (state : ConstructionState) : Prop :=
  ∀ id snapshot, state.destinationResumptions.lookup id = some snapshot →
    ResumptionBackingSource state id snapshot

def UnsupportedResumptionKeys (state : ConstructionState) : Prop :=
  ∀ id snapshot, state.destinationResumptions.lookup id = some snapshot →
    ¬ ReplacementSupported state id

def InactiveBackingExtension (before after : ConstructionState) : Prop :=
  ∀ (id : DestinationId) (row : PendingDestination), before.destinations[id]? = some row → activeProgress row.progress = false →
    ∃ current : PendingDestination, after.destinations[id]? = some current ∧ activeProgress current.progress = false ∧
      current.backing = row.backing

theorem resumptionBackingSource_child_storage (state : ConstructionState)
    (links : DestinationForwardLinks state) (id parent count : Nat)
    (snapshot owner : PendingDestination) (source : ResumptionBackingSource state id snapshot)
    (use : snapshot.use = .child parent) (present : state.destinations[parent]? = some owner)
    (suspended : owner.progress = .suspended count id) :
    snapshot.backing.receiverStorage = owner.storage := by
  obtain ⟨current, found, _, backing⟩ := source
  have edge := links parent owner present
  simp only [DestinationForwardLink, suspended] at edge
  obtain ⟨selected, selectedPresent, _, selectedBacking⟩ := edge
  have equal : selected = current := Option.some.inj (selectedPresent.symm.trans found)
  subst selected
  simp only [SnapshotBackingAgrees, use] at backing
  exact backing.trans selectedBacking

theorem resumptionBackingSource_replacement_backing (state : ConstructionState)
    (links : DestinationForwardLinks state) (id parent count : Nat)
    (snapshot owner : PendingDestination) (source : ResumptionBackingSource state id snapshot)
    (use : snapshot.use = .replacement parent) (present : state.destinations[parent]? = some owner)
    (exiting : owner.progress = .exiting count id) : snapshot.backing = owner.backing := by
  obtain ⟨current, found, _, backing⟩ := source
  have edge := links parent owner present
  simp only [DestinationForwardLink, exiting] at edge
  obtain ⟨selected, selectedPresent, _, selectedBacking⟩ := edge
  have equal : selected = current := Option.some.inj (selectedPresent.symm.trans found)
  subst selected
  simp only [SnapshotBackingAgrees, use] at backing
  exact backing.trans selectedBacking

theorem resumptionSource_backing (state : ConstructionState) (id : DestinationId)
    (snapshot : PendingDestination) (source : ResumptionSource state id snapshot) :
    ResumptionBackingSource state id snapshot := by
  obtain ⟨current, found, inactive, use, backing⟩ := source
  refine ⟨current, found, inactive, ?_⟩
  cases kind : snapshot.use <;> simp only [SnapshotBackingAgrees, kind, OwnershipLinkBacking, use] at backing ⊢
  · trivial
  all_goals exact backing

theorem inactiveBackingExtension_refl (state : ConstructionState) :
    InactiveBackingExtension state state := by
  intro id row present inactive
  exact ⟨row, present, inactive, rfl⟩

theorem inactiveBackingExtension_trans (before middle after : ConstructionState)
    (first : InactiveBackingExtension before middle) (second : InactiveBackingExtension middle after) :
    InactiveBackingExtension before after := by
  intro id row present inactive
  obtain ⟨interim, found, interimInactive, backing⟩ := first id row present inactive
  obtain ⟨current, currentPresent, currentInactive, currentBacking⟩ := second id interim found interimInactive
  exact ⟨current, currentPresent, currentInactive, currentBacking.trans backing⟩

theorem resumptionBackingSources_extension (before after : ConstructionState)
    (extension : InactiveBackingExtension before after)
    (resumptions : after.destinationResumptions = before.destinationResumptions)
    (sources : ResumptionBackingSources before) : ResumptionBackingSources after := by
  intro id snapshot present
  rw [resumptions] at present
  obtain ⟨row, found, inactive, backing⟩ := sources id snapshot present
  obtain ⟨current, currentPresent, currentInactive, currentBacking⟩ := extension id row found inactive
  refine ⟨current, currentPresent, currentInactive, ?_⟩
  cases use : snapshot.use with
  | receiver => simp only [SnapshotBackingAgrees, use]
  | child parent => simpa only [SnapshotBackingAgrees, use, currentBacking] using backing
  | replacement parent => simpa only [SnapshotBackingAgrees, use, currentBacking] using backing

theorem unsupportedResumptionKeys_extension (before after : ConstructionState)
    (extension : ReplacementSupportExtension before after)
    (resumptions : after.destinationResumptions = before.destinationResumptions)
    (sources : ResumptionBackingSources before) (unsupported : UnsupportedResumptionKeys before) :
    UnsupportedResumptionKeys after := by
  intro id snapshot present supported
  have oldPresent : before.destinationResumptions.lookup id = some snapshot := by
    simpa only [resumptions] using present
  obtain ⟨row, found, _, _⟩ := sources id snapshot oldPresent
  exact unsupported id snapshot oldPresent
    (extension id (Array.getElem?_eq_some_iff.mp found).1 supported)

theorem initial_resumptionBackingSources : ResumptionBackingSources .initial := by
  intro id snapshot present
  simp [ConstructionState.initial] at present

theorem initial_unsupportedResumptionKeys : UnsupportedResumptionKeys .initial := by
  intro id snapshot present
  simp [ConstructionState.initial] at present

end Goose.Proofs.ConstructionExecutionOwnership
