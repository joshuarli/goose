import Goose.Lower.Validation.ExpressionTypingGraphExtension
import Goose.Lower.GeneratedTargetFrames
import Goose.Lower.Validation.DefinitionSites

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem permissionFunc_edges_framed {le : LEnv} {before after : LS} {loop : Option LoopCtx}
    (extension : before.Ext after) (frames : LoopBuilderFrames loop before)
    (framed : TermEdgesFramed loop before after)
    {block : GIR.Block} (blockMember : block ∈ (permissionFunc le after).blocks.toList)
    {term : Term} (member : Inst.term term ∈ block.insts) {edge : BlockId × List ValueId}
    (edgeMember : edge ∈ term.permissionEdges) (bounded : edge.1 < before.blocks.size)
    {destination : GIR.Block} (row : (permissionFunc le after).blocks[edge.1]? = some destination) :
    (∃ old, old ∈ (permissionFunc le before).blocks.toList ∧ Inst.term term ∈ old.insts) ∨
      (∀ param ∈ destination.params, ∃ intTy, param.2 = .data (.int intTy)) := by
  obtain ⟨index, blockRow⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp blockMember)
  simp only [permissionFunc, Array.getElem?_map, Option.map_eq_some_iff] at blockRow
  obtain ⟨actual, actualRow, shape⟩ := blockRow
  subst block
  rcases framed index actual term edge.1 actualRow member (permissionEdge_target edgeMember) bounded with
    ⟨old, oldRow, instruction⟩ | target
  · exact Or.inl ⟨⟨old.params, old.insts.toList⟩,
      by simp only [permissionFunc, Array.toList_map, List.mem_map]
         exact ⟨old, Array.mem_toList_iff.mpr (Array.mem_of_getElem? oldRow), rfl⟩,
      instruction⟩
  · obtain ⟨old, oldRow, paramShapes⟩ := frames.targetParams target
    have mappedRow : (permissionFunc le before).blocks[edge.1]? = some ⟨old.params, old.insts.toList⟩ := by
      simp only [permissionFunc, Array.getElem?_map, oldRow, Option.map_some]
    obtain ⟨next, nextRow, params, _⟩ := permissionFunc_ext_at extension mappedRow
    have same := Option.some.inj (row.symm.trans nextRow)
    subst next
    apply Or.inr
    intro param paramMember
    rw [params] at paramMember
    rcases paramShapes with empty | ⟨id, intTy, singleton⟩
    · simp [empty] at paramMember
    · simp only [singleton, List.mem_singleton] at paramMember
      subst param
      exact ⟨intTy, rfl⟩

theorem permissionFunc_old_definition {le : LEnv} {before after : LS}
    (beforeDense : before.DenseDefinitions) (afterDense : after.DenseDefinitions)
    (extension : before.Ext after) {block : GIR.Block}
    (blockMember : block ∈ (permissionFunc le after).blocks.toList) {value : ValueId} {op : Op}
    (member : Inst.def value op ∈ block.insts) (bounded : value < before.vals.size) :
    ∃ old, old ∈ (permissionFunc le before).blocks.toList ∧ Inst.def value op ∈ old.insts := by
  obtain ⟨index, blockRow⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp blockMember)
  simp only [permissionFunc, Array.getElem?_map, Option.map_eq_some_iff] at blockRow
  obtain ⟨actual, actualRow, shape⟩ := blockRow
  subst block
  obtain ⟨position, instructionRow⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨old, oldRow, oldInstruction⟩ := old_instruction_site beforeDense afterDense extension actualRow instructionRow bounded
  refine ⟨⟨old.params, old.insts.toList⟩, ?_, List.mem_iff_getElem?.mpr ⟨position, oldInstruction⟩⟩
  simp only [permissionFunc, Array.toList_map, List.mem_map]
  exact ⟨old, Array.mem_toList_iff.mpr (Array.mem_of_getElem? oldRow), rfl⟩

theorem permissionFunc_old_parameter_block {le : LEnv} {before after : LS}
    (beforeDense : before.DenseDefinitions) (afterDense : after.DenseDefinitions)
    (extension : before.Ext after) {index : BlockId} {block : GIR.Block}
    (row : (permissionFunc le after).blocks[index]? = some block) {param : ValueId × VTy}
    (member : param ∈ block.params) (bounded : param.1 < before.vals.size) : index < before.blocks.size := by
  simp only [permissionFunc, Array.getElem?_map, Option.map_eq_some_iff] at row
  obtain ⟨actual, actualRow, shape⟩ := row
  subst block
  obtain ⟨position, parameterRow⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨old, oldRow, _⟩ := old_parameter_site beforeDense afterDense extension actualRow parameterRow bounded
  exact (Array.getElem?_eq_some_iff.mp oldRow).1

theorem ContentsClosed.ext {le : LEnv} {before after : LS} {authorized : ValueId → Prop}
    {loop : Option LoopCtx} (beforeDense : before.DenseDefinitions) (afterDense : after.DenseDefinitions)
    (extension : before.Ext after) (grows : before.vals.size ≤ after.vals.size)
    (types : TypePrefix before after) (frames : LoopBuilderFrames loop before)
    (framed : TermEdgesFramed loop before after)
    (closed : ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized)
    (noninteger : NonIntegerParameters (permissionFunc le before) authorized) :
    ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals authorized := by
  apply closed.of_origins beforeDense afterDense extension grows types noninteger
  · intro block blockMember value op member bounded
    exact permissionFunc_old_definition beforeDense afterDense extension blockMember member bounded
  · intro index block row param member bounded
    exact permissionFunc_old_parameter_block beforeDense afterDense extension row member bounded
  · intro block blockMember term member edge edgeMember bounded destination row
    exact permissionFunc_edges_framed extension frames framed blockMember member edgeMember bounded row

theorem NonIntegerParameters.ext {le : LEnv} {before after : LS} {authorized : ValueId → Prop}
    (beforeDense : before.DenseDefinitions) (afterDense : after.DenseDefinitions)
    (extension : before.Ext after) (bounded : ∀ value, authorized value → value < before.vals.size)
    (checked : NonIntegerParameters (permissionFunc le before) authorized) :
    NonIntegerParameters (permissionFunc le after) authorized := by
  apply checked.of_parameter_origins extension bounded
  intro index block row param member bound
  exact permissionFunc_old_parameter_block beforeDense afterDense extension row member bound

#print axioms ContentsClosed.ext
#print axioms permissionFunc_edges_framed

end Goose.Lower.Validation
