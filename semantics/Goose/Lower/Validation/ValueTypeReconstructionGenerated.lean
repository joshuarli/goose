import Goose.Lower.Validation.ValueTypeReconstructionOperations
import Goose.Lower.Validation.DenseDefinitions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem partition_flatMap {α β : Type} (left right : α → List β) (items : List α) :
    (items.flatMap fun item => left item ++ right item).Perm
      (items.flatMap left ++ items.flatMap right) := by
  induction items with
  | nil => exact .refl _
  | cons item rest ih =>
    have first := List.Perm.append_left (left item ++ right item) ih
    have swap := List.Perm.append_left (left item)
      ((List.perm_append_comm (l₁ := right item) (l₂ := rest.flatMap left)).append_right
        (rest.flatMap right))
    have first' : ((item :: rest).flatMap fun item => left item ++ right item).Perm
        ((left item ++ right item) ++ (rest.flatMap left ++ rest.flatMap right)) := first
    have second' : ((left item ++ right item) ++ (rest.flatMap left ++ rest.flatMap right)).Perm
        ((item :: rest).flatMap left ++ (item :: rest).flatMap right) := by
      simpa only [List.flatMap_cons, List.append_assoc] using swap
    exact first'.trans second'

private def blockInstructionResults (block : GIR.Block) : List ValueId :=
  block.insts.filterMap fun | .def value _ => some value | _ => none

theorem dense_function_covers {func : Func}
    (dense : (func.blocks.toList.flatMap GIR.Block.defs).Perm (List.range func.numValues)) :
    ∀ value, value < func.numValues →
      (∃ block ∈ func.blocks.toList, ∃ ty, (value, ty) ∈ block.params) ∨
      (∃ block ∈ func.blocks.toList, ∃ op, .def value op ∈ block.insts) := by
  intro value bound
  have member := dense.mem_iff.mpr (List.mem_range.mpr bound)
  obtain ⟨block, blockMember, definition⟩ := List.mem_flatMap.mp member
  rcases List.mem_append.mp definition with parameter | instruction
  · obtain ⟨⟨id, ty⟩, member, same⟩ := List.mem_map.mp parameter
    dsimp at same
    subst id
    exact Or.inl ⟨block, blockMember, ty, member⟩
  · obtain ⟨inst, member, result⟩ := List.mem_filterMap.mp instruction
    cases inst with
    | «def» id op =>
      cases result
      exact Or.inr ⟨block, blockMember, op, member⟩
    | eff effect => cases result
    | term term => cases result

theorem dense_function_parameter_separation {func : Func}
    (dense : (func.blocks.toList.flatMap GIR.Block.defs).Perm (List.range func.numValues)) :
    ∀ block ∈ func.blocks.toList, ∀ value ty, (value, ty) ∈ block.params →
      ∀ destination ∈ func.blocks.toList, ∀ op, .def value op ∈ destination.insts → False := by
  have unique : (func.blocks.toList.flatMap GIR.Block.defs).Nodup :=
    dense.symm.nodup List.nodup_range
  have partition := partition_flatMap (fun block : GIR.Block => block.params.map (·.1))
    blockInstructionResults func.blocks.toList
  have separated :
      ((func.blocks.toList.flatMap fun block => block.params.map (·.1)) ++
        func.blocks.toList.flatMap blockInstructionResults).Nodup :=
    partition.nodup unique
  have disjoint := (List.nodup_append.mp separated).2.2
  intro block blockMember value ty parameter destination destinationMember op definition
  exact disjoint value (List.mem_flatMap.mpr
      ⟨block, blockMember, List.mem_map.mpr ⟨(value, ty), parameter, rfl⟩⟩)
    value (List.mem_flatMap.mpr ⟨destination, destinationMember,
      List.mem_filterMap.mpr ⟨.def value op, definition, rfl⟩⟩) rfl

theorem dense_function_rank_bound {func : Func} {value : ValueId}
    (bound : value < func.numValues) : value < 2 * func.numValues + 2 := by
  exact Nat.lt_of_lt_of_le bound
    (Nat.le_add_right_of_le (Nat.le_mul_of_pos_left _ (by decide)))

theorem rankedReconstruction_of_dense {module : GIR.Module} {func : Func}
    {types : ValueId → VTy}
    (dense : (func.blocks.toList.flatMap GIR.Block.defs).Perm (List.range func.numValues))
    (parameters : ∀ block ∈ func.blocks.toList, ∀ value ty,
      (value, ty) ∈ block.params → ty = types value)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op,
      .def value op ∈ block.insts →
      ReconstructionReady module func types id value op) :
    RankedReconstruction module func types id := by
  refine ⟨parameters, dense_function_parameter_separation dense, ?_,
    fun _ bound => dense_function_rank_bound bound, ?_⟩
  · intro value bound
    rcases dense_function_covers dense value bound with parameter | definition
    · obtain ⟨block, member, ty, param⟩ := parameter
      have agrees := parameters block member value ty param
      subst ty
      exact Or.inl ⟨block, member, param⟩
    · exact Or.inr definition
  · intro block member value op definition bound
    exact definitions block member value op definition

theorem valueTypes_reconstructs_of_dense {module : GIR.Module} {func : Func}
    {types : ValueId → VTy}
    (dense : (func.blocks.toList.flatMap GIR.Block.defs).Perm (List.range func.numValues))
    (parameters : ∀ block ∈ func.blocks.toList, ∀ value ty,
      (value, ty) ∈ block.params → ty = types value)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op,
      .def value op ∈ block.insts →
      ReconstructionReady module func types id value op) :
    ∀ value, value < func.numValues →
      (func.valueTypes module)[value]? = some (some (types value)) :=
  valueTypes_ranked_reconstructs (rankedReconstruction_of_dense dense parameters definitions)

end Goose.Lower.Validation
