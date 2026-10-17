import Goose.Lower.Validation.ExpressionTypingGraphFrame

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem permissionFunc_ext_at {le : LEnv} {before after : LS} (extension : before.Ext after)
    {index : BlockId} {block : GIR.Block} (row : (permissionFunc le before).blocks[index]? = some block) :
    ∃ next, (permissionFunc le after).blocks[index]? = some next ∧ next.params = block.params ∧
      ∃ suffix, next.insts = block.insts ++ suffix := by
  simp only [permissionFunc, Array.getElem?_map, Option.map_eq_some_iff] at row ⊢
  obtain ⟨actual, actualRow, shape⟩ := row
  subst block
  obtain ⟨next, nextRow, params, suffix, instructions⟩ := extension.2 index actual actualRow
  exact ⟨⟨next.params, next.insts.toList⟩, ⟨next, nextRow, rfl⟩, params, suffix, instructions⟩

theorem permissionFunc_old_target {le : LEnv} {before after : LS} (extension : before.Ext after)
    {index : BlockId} (bounded : index < before.blocks.size) {block : GIR.Block}
    (row : (permissionFunc le after).blocks[index]? = some block) :
    ∃ old, (permissionFunc le before).blocks[index]? = some old ∧ block.params = old.params := by
  have oldRow : (permissionFunc le before).blocks[index]? =
      some ((permissionFunc le before).blocks[index]'(by simpa only [permissionFunc, Array.size_map] using bounded)) := by
    exact Array.getElem?_eq_getElem (by simpa only [permissionFunc, Array.size_map] using bounded)
  obtain ⟨next, nextRow, params, _⟩ := permissionFunc_ext_at extension oldRow
  have same := Option.some.inj (row.symm.trans nextRow)
  subst next
  exact ⟨_, oldRow, params⟩

theorem NonIntegerParameters.of_parameter_origins {le : LEnv} {before after : LS}
    {authorized : ValueId → Prop} (extension : before.Ext after)
    (checked : NonIntegerParameters (permissionFunc le before) authorized)
    (bounded : ∀ value, authorized value → value < before.vals.size)
    (parameters : ∀ index block, (permissionFunc le after).blocks[index]? = some block →
      ∀ param ∈ block.params, param.1 < before.vals.size → index < before.blocks.size) :
    NonIntegerParameters (permissionFunc le after) authorized := by
  intro block blockMember param member permitted
  obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp blockMember)
  have indexBound := parameters index block row param member (bounded _ permitted)
  obtain ⟨old, oldRow, params⟩ := permissionFunc_old_target extension indexBound row
  exact checked old (Array.mem_toList_iff.mpr (Array.mem_of_getElem? oldRow)) param
    (by rw [← params]; exact member) permitted

theorem ContentsClosed.of_origins {le : LEnv} {before after : LS} {authorized : ValueId → Prop}
    (beforeDense : before.DenseDefinitions) (afterDense : after.DenseDefinitions)
    (extension : before.Ext after) (grows : before.vals.size ≤ after.vals.size)
    (types : TypePrefix before after)
    (closed : ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized)
    (noninteger : NonIntegerParameters (permissionFunc le before) authorized)
    (definitions : ∀ block ∈ (permissionFunc le after).blocks.toList,
      ∀ value op, Inst.def value op ∈ block.insts → value < before.vals.size →
        ∃ old, old ∈ (permissionFunc le before).blocks.toList ∧ Inst.def value op ∈ old.insts)
    (parameters : ∀ index block, (permissionFunc le after).blocks[index]? = some block →
      ∀ param ∈ block.params, param.1 < before.vals.size → index < before.blocks.size)
    (edges : ∀ block ∈ (permissionFunc le after).blocks.toList,
      ∀ term, Inst.term term ∈ block.insts → ∀ edge ∈ term.permissionEdges,
      edge.1 < before.blocks.size → ∀ destination,
      (permissionFunc le after).blocks[edge.1]? = some destination →
      (∃ old, old ∈ (permissionFunc le before).blocks.toList ∧ Inst.term term ∈ old.insts) ∨
        (∀ param ∈ destination.params, ∃ intTy, param.2 = .data (.int intTy))) :
    ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals authorized := by
  have oldBound : ∀ value, authorized value → value < before.vals.size := by
    intro value member
    simpa only [permissionFunc_numValues beforeDense le] using closed.bounded value member
  constructor
  · intro value member
    rw [permissionFunc_numValues afterDense le]
    exact Nat.lt_of_lt_of_le (oldBound value member) grows
  · intro block row param member permitted
    have indexBound := parameters 0 block row param member (oldBound _ permitted)
    obtain ⟨old, oldRow, params⟩ := permissionFunc_old_target extension indexBound row
    exact typedPermissions_retained types (closed.entry old oldRow param (by rw [← params]; exact member) permitted)
  · intro block blockMember value op member permitted
    obtain ⟨old, oldMember, instruction⟩ := definitions block blockMember value op member (oldBound value permitted)
    exact (closed.definitions old oldMember value op instruction permitted).retained types
  · intro block blockMember term member edge edgeMember destination row entry entryMember permitted
    have indexBound := parameters edge.1 destination row entry.1 (List.of_mem_zip entryMember).1 (oldBound _ permitted)
    obtain ⟨oldDestination, oldRow, params⟩ := permissionFunc_old_target extension indexBound row
    have oldEntry : entry ∈ oldDestination.params.zip edge.2 := by rw [← params]; exact entryMember
    rcases edges block blockMember term member edge edgeMember indexBound destination row with
      ⟨old, oldMember, instruction⟩ | integerParams
    · exact closed.edges old oldMember term instruction edge edgeMember oldDestination oldRow entry oldEntry permitted
    · obtain ⟨intTy, shape⟩ := integerParams entry.1 (List.of_mem_zip entryMember).1
      have impossible := noninteger oldDestination
        (Array.mem_toList_iff.mpr (Array.mem_of_getElem? oldRow)) entry.1 (List.of_mem_zip oldEntry).1 permitted intTy
      exact (impossible shape).elim

#print axioms ContentsClosed.of_origins

end Goose.Lower.Validation
