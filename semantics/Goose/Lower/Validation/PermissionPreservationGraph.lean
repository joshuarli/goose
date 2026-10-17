import Goose.Lower.Validation.PermissionPreservationEdges
import Goose.Lower.Validation.ExpressionTypingGraphTargets

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem WritableClosed.of_origins {le : LEnv} {before after : LS} {authorized contents : ValueId → Prop}
    (beforeDense : before.DenseDefinitions) (afterDense : after.DenseDefinitions)
    (extension : before.Ext after) (grows : before.vals.size ≤ after.vals.size)
    (types : TypePrefix before after)
    (closed : WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized contents)
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
    WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals authorized contents := by
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
    exact typedPermissions_binding_retained types (closed.entry old oldRow param (by rw [← params]; exact member) permitted)
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


theorem WritableClosed.ext {le : LEnv} {before after : LS} {authorized contents : ValueId → Prop}
    {loop : Option LoopCtx} (beforeDense : before.DenseDefinitions) (afterDense : after.DenseDefinitions)
    (extension : before.Ext after) (grows : before.vals.size ≤ after.vals.size)
    (types : TypePrefix before after) (frames : LoopBuilderFrames loop before)
    (framed : TermEdgesFramed loop before after)
    (closed : WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized contents)
    (noninteger : NonIntegerParameters (permissionFunc le before) authorized) :
    WritableClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals authorized contents := by
  apply closed.of_origins beforeDense afterDense extension grows types noninteger
  · intro block blockMember value op member bounded
    exact permissionFunc_old_definition beforeDense afterDense extension blockMember member bounded
  · intro index block row param member bounded
    exact permissionFunc_old_parameter_block beforeDense afterDense extension row member bounded
  · intro block blockMember term member edge edgeMember bounded destination row
    exact permissionFunc_edges_framed extension frames framed blockMember member edgeMember bounded row


#print axioms WritableClosed.of_origins
#print axioms WritableClosed.ext

end Goose.Lower.Validation
