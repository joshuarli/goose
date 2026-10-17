import Goose.Lower.Validation.ReplacementScopedOriginQueries
import Goose.Lower.Validation.ReplacementApartUnion

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR Goose.GIR.ReplacementContentFlow.Model

private theorem collect_apart_queries {query : ValueId → Option (List RootRef)}
    {queries : ReplacementQueries} {owner : ValueId} {values : List ValueId}
    (known : ∀ value ∈ values, ∃ roots, query value = some roots ∧
      ReplacementApart queries owner (some roots)) :
    ∃ rows, values.mapM query = some rows ∧
      ∀ row ∈ rows, ReplacementApart queries owner (some row) := by
  induction values with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons first rest ih =>
    obtain ⟨roots, rootAt, apart⟩ := known first (by simp)
    obtain ⟨rows, rowsAt, apartRows⟩ := ih (fun value member => known value (by simp [member]))
    refine ⟨roots :: rows, ?_, ?_⟩
    · simp [List.mapM_cons, rootAt, rowsAt]
    · intro row member
      rcases List.mem_cons.mp member with same | later
      · simpa only [same] using apart
      · exact apartRows row later

theorem forFunction_scoped_origin_apart {module : GIR.Module} {env : PEnv} {root : DemandNode}
    {func : Func} {types : Array (Option VTy)} {upper : Prov} {first last value : ValueId}
    {returned : List RootRef} {queries : ReplacementQueries} {owner : ValueId}
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
    (leaves : ∀ value, ScopedOrigin env root func types upper first last value →
      ScopedOriginLeaf env root func types upper value →
      ∃ dependencies, ((replacementContentFlow module).forFunction func types).ownerDependencies value = some dependencies ∧
        ReplacementApart queries owner (some dependencies))
    (chosen : ScopedOrigin env root func types upper first last value)
    (known : ((replacementContentFlow module).forFunction func types).value value = some returned) :
    ∃ dependencies, ((replacementContentFlow module).forFunction func types).ownerDependencies value = some dependencies ∧
      ReplacementApart queries owner (some dependencies) := by
  classical
  let leafValues := scopedOriginLeaves env root func types upper first last
  obtain ⟨rows, rowsAt, apartRows⟩ := collect_apart_queries (values := leafValues)
    (fun value member => leaves value (mem_scopedOriginLeaves.mp member).2.1
      (mem_scopedOriginLeaves.mp member).2.2)
  obtain ⟨dependencies, dependencyAt, included⟩ := forFunction_scoped_origin_dependencies
    canonical unique values globals fields typing uses references entryBefore incoming bounded
    (fun value selected leaf => ReplacementContentFlow.Model.known_root_queries_mem rowsAt
      (mem_scopedOriginLeaves.mpr ⟨selected.2.1, selected, leaf⟩)) chosen known
  exact ⟨dependencies, dependencyAt, ReplacementApart.of_flatten_subset apartRows included⟩

#print axioms forFunction_scoped_origin_apart

end Goose.Lower.Validation.ReplacementContentFlowSource
