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

theorem SnapshotContentsWitness.emitTerm {le : LEnv}
    {first snapshot owner : ValueId} {authorized : ValueId → Prop} {before after : LS}
    {term : Term} {result : Unit}
    (witness : SnapshotContentsWitness le first snapshot owner authorized before)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : Goose.Lower.emitTerm term le before = (result, after))
    (edges : ∀ edge ∈ term.permissionEdges, ∀ destination,
      (permissionFunc le before).blocks[edge.1]? = some destination →
      ∀ entry ∈ destination.params.zip edge.2, authorized entry.1.1 → authorized entry.2) :
    SnapshotContentsWitness le first snapshot owner authorized after := by
  cases live : before.cur with
  | none =>
    rw [emitTerm_none term le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact witness
  | some current =>
    exact ⟨witness.closed.emitTerm checked bounded live run edges,
      witness.noninteger.emitTerm live run, witness.ownerMember, witness.fresh, witness.beforeSnapshot⟩

theorem SnapshotContentsWitness.emitTerm_before {le : LEnv}
    {first snapshot owner : ValueId} {authorized : ValueId → Prop} {before after : LS}
    {term : Term} {result : Unit}
    (witness : SnapshotContentsWitness le first snapshot owner authorized before)
    (generated : GeneratedBuilderState before)
    (run : Goose.Lower.emitTerm term le before = (result, after))
    (earlier : ∀ edge ∈ term.permissionEdges, ∀ destination,
      (permissionFunc le before).blocks[edge.1]? = some destination →
      ∀ parameter ∈ destination.params, parameter.1 < first) :
    SnapshotContentsWitness le first snapshot owner authorized after := by
  apply witness.emitTerm generated.dense generated.live run
  intro edge member destination row entry belongs permitted
  exact (Nat.not_lt_of_ge (witness.fresh _ permitted)
    (earlier edge member destination row entry.1 (List.of_mem_zip belongs).1)).elim

theorem snapshot_definition_lt {state : LS} {snapshot owner : ValueId} {mode : SnapshotMode}
    (checked : state.DenseDefinitions) (member : .def snapshot (.snapshot mode owner) ∈ state.insts) :
    snapshot < state.vals.size := by
  apply checked.mem_lt
  obtain ⟨block, belongs, defined⟩ := List.mem_flatMap.mp member
  apply List.mem_flatMap.mpr
  refine ⟨block, belongs, ?_⟩
  simp only [BlockB.defs, List.mem_append]
  exact Or.inr (List.mem_filterMap.mpr ⟨.def snapshot (.snapshot mode owner), defined, rfl⟩)

theorem snapshot_instruction_before {before after : LS} {snapshot owner : ValueId} {mode : SnapshotMode}
    (beforeDense : before.DenseDefinitions) (afterDense : after.DenseDefinitions)
    (extension : before.Ext after) (bounded : snapshot < before.vals.size)
    (member : .def snapshot (.snapshot mode owner) ∈ after.insts) :
    .def snapshot (.snapshot mode owner) ∈ before.insts := by
  obtain ⟨block, blockMember, defined⟩ := List.mem_flatMap.mp member
  obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp blockMember)
  obtain ⟨position, instruction⟩ := List.mem_iff_getElem?.mp defined
  obtain ⟨prior, priorRow, priorInstruction⟩ :=
    old_instruction_site beforeDense afterDense extension row instruction bounded
  exact List.mem_flatMap.mpr ⟨prior, Array.mem_toList_iff.mpr (Array.mem_of_getElem? priorRow),
    List.mem_iff_getElem?.mpr ⟨position, priorInstruction⟩⟩

end Goose.Lower.Validation
