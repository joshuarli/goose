import Goose.GIR.ReplacementContentFlowProofsScopedQueries
import Goose.GIR.ReplacementContentFlowProofsScopedEdges

namespace Goose.GIR

open Goose.Core ReplacementContentFlow.Model

theorem ReplacementContentFlow.forFunction_backing_dependencies {module : Module}
    {func : Func} {types : Array (Option VTy)} {block : Block} {value source : ValueId} {op : Op}
    {returned sourceDependencies : List RootRef}
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup)
    (member : block ∈ func.blocks.toList) (defined : Inst.def value op ∈ block.insts)
    (backing : BackingOp op source)
    (reference : valRefLike (func.valueTypes module) value = true)
    (valueBound : value < func.numValues) (sourceBound : source < func.numValues)
    (sourceKnown : ((replacementContentFlow module).forFunction func types).ownerDependencies source =
      some sourceDependencies)
    (valueKnown : ((replacementContentFlow module).forFunction func types).value value = some returned) :
    ∃ dependencies, ((replacementContentFlow module).forFunction func types).ownerDependencies value = some dependencies ∧
      dependencies ⊆ sourceDependencies := by
  have selectedRoot : ∀ candidate, candidate = value ∨ candidate = source → candidate ∉ [source] → candidate = value := by
    intro candidate selected nonleaf
    exact selected.resolve_right (fun same => nonleaf (by simp [same]))
  have known : [source].mapM (((replacementContentFlow module).forFunction func types).ownerDependencies) =
      some [sourceDependencies] := by simp [List.mapM_cons, sourceKnown]
  obtain ⟨dependencies, dependenciesAt, included⟩ := ReplacementContentFlow.forFunction_scoped_dependencies
    (module := module) (func := func) (types := types)
    (selected := fun candidate => candidate = value ∨ candidate = source) (leaves := [source])
    (bounded := fun candidate selected => by rcases selected with rfl | rfl <;> assumption)
    (separate := fun entry entryAt candidate selected nonleaf parameter => by
      have same := selectedRoot candidate selected nonleaf
      subst candidate
      exact unique_definition_not_parameter unique member defined entry
        (Array.mem_toList_iff.mpr (Array.mem_of_getElem? entryAt)) parameter)
    (definitions := fun actualBlock actualMember candidate actualOp actualDefined selected => by
      by_cases leaf : candidate ∈ [source]
      · exact Or.inl leaf
      · have same := selectedRoot candidate selected leaf
        subst candidate
        have sameOp := unique_definition_op unique actualMember actualDefined member defined
        subst actualOp
        exact Or.inr ⟨source, Or.inr rfl, backing.noncall, backing.result reference⟩)
    (incoming := fun candidate selected nonleaf input incoming => by
      have same := selectedRoot candidate selected nonleaf
      subst candidate
      exact False.elim (allIncomingValues_absent_of_definition unique member defined incoming))
    known (Or.inl rfl) valueKnown
  exact ⟨dependencies, dependenciesAt, by simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using included⟩

#print axioms ReplacementContentFlow.forFunction_backing_dependencies

end Goose.GIR
