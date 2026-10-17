import Goose.Lower.Validation.SnapshotContentsSource

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem SnapshotSourceTrace.patchBrs_before {le : LEnv} {first : ValueId}
    {captured before after : LS} {target : BlockId} {result : Unit}
    (trace : SnapshotSourceTrace le first captured before) (incoming : List (BlockId × ValueId))
    (generated : GeneratedBuilderState before)
    (run : patchBrs target incoming le before = (result, after))
    (earlier : ∀ destination, (permissionFunc le before).blocks[target]? = some destination →
      ∀ parameter ∈ destination.params, parameter.1 < first) :
    SnapshotSourceTrace le first captured after := by
  intro snapshot mode owner member bound
  obtain ⟨site, fresh, extension, types, retained⟩ := trace snapshot mode owner member bound
  refine ⟨site, fresh, extension.trans (adv_patchBrs_ext incoming run),
    types.trans (types_patchBrs target incoming le before result after run), retained.trans ?_⟩
  intro authorized witness
  apply witness.patchBrs_before incoming generated run
  intro destination row parameter belongs
  exact Nat.lt_of_lt_of_le (earlier destination row parameter belongs) fresh

theorem SnapshotSourceTrace.patchBrs_after {le : LEnv} {first : ValueId}
    {captured before after : LS} {target : BlockId} {result : Unit}
    (trace : SnapshotSourceTrace le first captured before) (incoming : List (BlockId × ValueId))
    (checked : captured.DenseDefinitions) (generated : GeneratedBuilderState before)
    (run : patchBrs target incoming le before = (result, after))
    (later : ∀ destination, (permissionFunc le before).blocks[target]? = some destination →
      ∀ parameter ∈ destination.params, captured.vals.size ≤ parameter.1) :
    SnapshotSourceTrace le first captured after := by
  intro snapshot mode owner member bound
  obtain ⟨site, fresh, extension, types, retained⟩ := trace snapshot mode owner member bound
  refine ⟨site, fresh, extension.trans (adv_patchBrs_ext incoming run),
    types.trans (types_patchBrs target incoming le before result after run), retained.trans ?_⟩
  intro authorized witness
  apply witness.patchBrs_after incoming generated run
  intro destination row parameter belongs
  exact Nat.le_trans (Nat.le_of_lt (snapshot_definition_lt checked member))
    (later destination row parameter belongs)

theorem SnapshotSourceTrace.emitTerm_before {le : LEnv} {first : ValueId}
    {captured before after : LS} {term : Term} {result : Unit}
    (trace : SnapshotSourceTrace le first captured before)
    (generated : GeneratedBuilderState before)
    (run : emitTerm term le before = (result, after))
    (earlier : ∀ edge ∈ term.permissionEdges, ∀ destination,
      (permissionFunc le before).blocks[edge.1]? = some destination →
      ∀ parameter ∈ destination.params, parameter.1 < first) :
    SnapshotSourceTrace le first captured after := by
  intro snapshot mode owner member bound
  obtain ⟨site, fresh, extension, types, retained⟩ := trace snapshot mode owner member bound
  refine ⟨site, fresh, extension.trans (advB_emitTerm term le before result after run).ext,
    types.trans (types_emitTerm term le before result after run), retained.trans ?_⟩
  intro authorized witness
  apply witness.emitTerm_before generated run
  intro edge edgeMember destination row parameter belongs
  exact Nat.lt_of_lt_of_le (earlier edge edgeMember destination row parameter belongs) fresh

theorem SnapshotSourceTrace.setCur {le : LEnv} {first : ValueId}
    {captured before after : LS} {current : Option BlockId} {result : Unit}
    (trace : SnapshotSourceTrace le first captured before)
    (run : Goose.Lower.setCur current le before = (result, after)) :
    SnapshotSourceTrace le first captured after := by
  have extension : before.Ext after := by
    rw [setCur_run] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact .refl _
  intro snapshot mode owner member bound
  obtain ⟨site, fresh, extended, types, retained⟩ := trace snapshot mode owner member bound
  exact ⟨site, fresh, extended.trans extension,
    types.trans (types_setCur current le before result after run),
    retained.trans (fun _ witness => witness.setCur run)⟩

end Goose.Lower.Validation
