import Goose.Lower.Validation.SnapshotContents

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem SnapshotContentsWitness.patchTerm {le : LEnv}
    {first snapshot owner : ValueId} {authorized : ValueId → Prop} {before after : LS}
    {current : BlockId} {term : Term} {result : Unit}
    (witness : SnapshotContentsWitness le first snapshot owner authorized before)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : Goose.Lower.patchTerm current term le before = (result, after))
    (edges : ∀ edge ∈ term.permissionEdges, ∀ destination,
      (permissionFunc le before).blocks[edge.1]? = some destination →
      ∀ entry ∈ destination.params.zip edge.2, authorized entry.1.1 → authorized entry.2) :
    SnapshotContentsWitness le first snapshot owner authorized after := by
  exact ⟨witness.closed.patchTerm checked bounded run edges,
    witness.noninteger.patchTerm run, witness.ownerMember, witness.fresh, witness.beforeSnapshot⟩

theorem SnapshotContentsWitness.patchTerm_avoiding_targets {le : LEnv}
    {first snapshot owner : ValueId} {authorized : ValueId → Prop} {before after : LS}
    {current : BlockId} {term : Term} {result : Unit}
    (witness : SnapshotContentsWitness le first snapshot owner authorized before)
    (generated : GeneratedBuilderState before)
    (run : Goose.Lower.patchTerm current term le before = (result, after))
    (excluded : ∀ edge ∈ term.permissionEdges, ∀ destination,
      (permissionFunc le before).blocks[edge.1]? = some destination →
      ∀ param ∈ destination.params, ¬ authorized param.1) :
    SnapshotContentsWitness le first snapshot owner authorized after := by
  apply witness.patchTerm generated.dense generated.live run
  intro edge member destination row entry belongs permitted
  exact (excluded edge member destination row entry.1 (List.of_mem_zip belongs).1 permitted).elim

theorem SnapshotContentsWitness.patchBrs0 {le : LEnv}
    {first snapshot owner : ValueId} {authorized : ValueId → Prop} {before after : LS}
    {target : BlockId} {result : Unit} (incoming : List BlockId)
    (witness : SnapshotContentsWitness le first snapshot owner authorized before)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : patchBrs0 target incoming le before = (result, after)) :
    SnapshotContentsWitness le first snapshot owner authorized after := by
  induction incoming generalizing before after result with
  | nil =>
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact witness
  | cons block rest ih =>
    obtain ⟨_, middle, patched, suffix⟩ := bind_eq.mp run
    apply ih (before := middle) (run := suffix)
    · apply witness.patchTerm checked bounded patched
      intro edge member destination row entry belongs
      have shape : edge = (target, []) := by simpa [Term.permissionEdges] using member
      subst edge
      simp at belongs
    · exact (dense_patchTerm block (.br target []) le before _ middle patched checked bounded).1
    · exact (dense_patchTerm block (.br target []) le before _ middle patched checked bounded).2.1

theorem SnapshotContentsWitness.setCur {le : LEnv}
    {first snapshot owner : ValueId} {authorized : ValueId → Prop} {before after : LS}
    {current : Option BlockId} {result : Unit}
    (witness : SnapshotContentsWitness le first snapshot owner authorized before)
    (run : setCur current le before = (result, after)) :
    SnapshotContentsWitness le first snapshot owner authorized after := by
  rw [setCur_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨witness.closed, witness.noninteger, witness.ownerMember, witness.fresh, witness.beforeSnapshot⟩

end Goose.Lower.Validation
