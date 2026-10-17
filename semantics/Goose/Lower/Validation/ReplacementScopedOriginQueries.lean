import Goose.Lower.Validation.ReplacementScopedOrigins

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR Goose.GIR.ReplacementContentFlow.Model

private theorem collect_leaf_queries {query : ValueId → Option (List RootRef)}
    {values : List ValueId} {ceiling : List RootRef}
    (known : ∀ value ∈ values, ∃ roots, query value = some roots ∧ roots ⊆ ceiling) :
    ∃ rows, values.mapM query = some rows ∧ rows.flatten ⊆ ceiling := by
  induction values with
  | nil => exact ⟨[],rfl,by simp⟩
  | cons first rest ih =>
      obtain ⟨roots,queryAt,subset⟩ := known first (by simp)
      obtain ⟨rows,rowsAt,subsets⟩ := ih (fun value member => known value (by simp [member]))
      refine ⟨roots :: rows,?_,?_⟩
      · simp [List.mapM_cons,queryAt,rowsAt]
      · intro root member
        rcases List.mem_append.mp (show root ∈ roots ++ rows.flatten from member) with first | rest
        · exact subset first
        · exact subsets rest

theorem forFunction_scoped_origin_dependencies {module : GIR.Module} {env : PEnv} {root : DemandNode}
    {func : Func} {types : Array (Option VTy)} {upper : Prov} {first last value : ValueId}
    {returned ceiling : List RootRef}
    (canonical : types = func.valueTypes module)
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup)
    (values : ValueTypeShapes types)
    (globals : ∀ (index : Nat) (type : Ty) (kind : VarKind),
      (module.tyEnv func).globals[index]? = some (type,kind) → type.isRefLike = false)
    (fields : ∀ (index : Nat) (descriptor : StructDef), (module.tyEnv func).structs[index]? = some descriptor →
      ∀ (fieldIndex : Nat) (field : StructField), descriptor.fields[fieldIndex]? = some field → field.ty.flat = true)
    (typing : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts, InstructionTyping module func types inst)
    (uses : ∀ block ∈ func.blocks.toList, ∀ value op, Inst.def value op ∈ block.insts →
      first ≤ value → value < last → ∀ source ∈ (Inst.def value op).uses, first ≤ source ∧ source < last)
    (references : ∀ block ∈ func.blocks.toList, ∀ value op, Inst.def value op ∈ block.insts →
      first ≤ value → value < last → ∀ source ∈ accessOperands (.def value op), ∀ mutability payload,
        types[source]? = some (some (.data (.ref mutability payload))) →
        ConsumedReferenceOccurrence env root func types upper source)
    (entryBefore : ∀ entry, func.blocks[0]? = some entry →
      ∀ value ∈ entry.params.map Prod.fst, value < first)
    (incoming : ∀ value, first ≤ value → value < last →
      ∀ source ∈ allIncomingValues func value, first ≤ source ∧ source < last)
    (bounded : last ≤ func.numValues)
    (leaves : ∀ value, ScopedOrigin env root func types upper first last value → ScopedOriginLeaf env root func types upper value →
      ∃ dependencies, ((replacementContentFlow module).forFunction func types).ownerDependencies value = some dependencies ∧
        dependencies ⊆ ceiling)
    (chosen : ScopedOrigin env root func types upper first last value)
    (known : ((replacementContentFlow module).forFunction func types).value value = some returned) :
    ∃ dependencies, ((replacementContentFlow module).forFunction func types).ownerDependencies value = some dependencies ∧
      dependencies ⊆ ceiling := by
  classical
  let leafValues := scopedOriginLeaves env root func types upper first last
  have leafMem : ∀ value, value ∈ leafValues ↔ value < last ∧ ScopedOrigin env root func types upper first last value ∧ ScopedOriginLeaf env root func types upper value := by
    intro value
    exact mem_scopedOriginLeaves
  obtain ⟨rows,rowsAt,rowBounds⟩ := collect_leaf_queries (values := leafValues)
    (fun value member => leaves value (leafMem value |>.mp member).2.1 (leafMem value |>.mp member).2.2)
  have actualDefinitions := ScopedOrigin.definitions unique values globals fields typing uses references
  have definitionClosure : ∀ block ∈ func.blocks.toList, ∀ value op, Inst.def value op ∈ block.insts →
      ScopedOrigin env root func types upper first last value → value ∈ leafValues ∨
        ∃ source, ScopedOrigin env root func types upper first last source ∧
          (∀ callee args origin, op ≠ .call callee args origin) ∧
          ∀ state, result func (func.valueTypes module) state value op = flowAt state.values source := by
    intro block member value op defined selected
    rcases actualDefinitions block member value op defined selected with leaf | forward
    · exact .inl ((leafMem value).mpr ⟨selected.2.1,selected,leaf⟩)
    · rw [← canonical]
      exact .inr forward
  obtain ⟨dependencies,dependenciesAt,subset⟩ := ReplacementContentFlow.forFunction_scoped_dependencies
    (bounded := fun value selected => Nat.lt_of_lt_of_le selected.2.1 bounded)
    (separate := fun entry entryAt value selected notLeaf member =>
      Nat.not_lt_of_ge selected.1 (entryBefore entry entryAt value member))
    (definitions := definitionClosure)
    (incoming := fun value selected notLeaf source input => ScopedOrigin.incoming unique typing selected
      (fun leaf => notLeaf ((leafMem value).mpr ⟨selected.2.1,selected,leaf⟩)) input
      (incoming value selected.1 selected.2.1 source input))
    rowsAt chosen known
  exact ⟨dependencies,dependenciesAt,fun root member => rowBounds (subset member)⟩

#print axioms forFunction_scoped_origin_dependencies

end Goose.Lower.Validation.ReplacementContentFlowSource
