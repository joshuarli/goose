import Goose.Lower.Validation.ReplacementProvenance
import Goose.Lower.Validation.DenseDefinitions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem definition_bounded_of_dense (func : Func)
    (dense : (func.blocks.toList.flatMap GIR.Block.defs).Perm (List.range func.numValues))
    (block : GIR.Block) (blockMember : block ∈ func.blocks.toList) (value : ValueId) (op : Op)
    (instruction : Inst.def value op ∈ block.insts) : value < func.numValues := by
  apply List.mem_range.mp
  apply dense.mem_iff.mp
  apply List.mem_flatMap.mpr
  refine ⟨block, blockMember, ?_⟩
  simp only [GIR.Block.defs, List.mem_append]
  apply Or.inr
  apply List.mem_filterMap.mpr
  exact ⟨.def value op, instruction, rfl⟩

theorem lowerContext_canonical_definition_bounds (module : Core.Module) (context : Context) (impl : Core.Impl) :
    ∀ block ∈ (lowerContextAt module context impl).blocks.toList, ∀ value op,
      Inst.def value op ∈ block.insts → value < (lowerContextAt module context impl).numValues :=
  definition_bounded_of_dense _ (lowerImpl_dense_definitions module impl)

theorem lowerGlobal_canonical_definition_bounds (module : Core.Module) (global : Core.Global) :
    ∀ block ∈ (lowerGlobal module global).init.blocks.toList, ∀ value op,
      Inst.def value op ∈ block.insts → value < (lowerGlobal module global).init.numValues :=
  definition_bounded_of_dense _ (lowerGlobal_dense_definitions module global)

theorem canonical_provenance_sizes (func : Func) (results : Array (List RootRef))
    (types : Array (Option VTy)) (rootCount : Nat) :
    (func.provenance results types rootCount).vals.size = func.numValues ∧
      (func.provenance results types rootCount).slots.size = func.slots.size := by
  have grows := provFix_extends results types func
    ((func.numValues + func.slots.size + 1) * (rootCount + 1)) (provStart types func)
  refine ⟨grows.2.1.trans (provStart_values_size func types), ?_⟩
  simpa only [Func.provenance, provStart, Func.slotRootSeeds, Array.size_mapIdx] using grows.1

#print axioms lowerContext_canonical_definition_bounds
#print axioms lowerGlobal_canonical_definition_bounds
#print axioms canonical_provenance_sizes

end Goose.Lower.Validation
