import Goose.Lower.Validation.ReplacementScopedOrigins
import Goose.Lower.Validation.ReplacementScopedCallsApart

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR ReplacementContentFlow.Model

def ScopedDemandLeaf (env : PEnv) (root : DemandNode) (func : Func)
    (types : Array (Option VTy)) (upper : Prov) (value : ValueId) : Prop :=
  (∃ mutability payload, types[value]? = some (some (.data (.ref mutability payload))) ∧
    ConsumedReferenceOccurrence env root func types upper value ∧ ¬ ScopedTypedBacking func types value) ∨
  ∃ block address, block ∈ func.blocks.toList ∧ Inst.def value (.load address) ∈ block.insts

noncomputable def scopedDemandLeaves (env : PEnv) (root : DemandNode) (func : Func)
    (types : Array (Option VTy)) (upper : Prov) (first last : ValueId) : List ValueId := by
  classical
  exact (List.range last).filter (fun value => ScopedOrigin env root func types upper first last value ∧
    ScopedDemandLeaf env root func types upper value)

theorem mem_scopedDemandLeaves {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {first last value : ValueId} :
    value ∈ scopedDemandLeaves env root func types upper first last ↔
      value < last ∧ ScopedOrigin env root func types upper first last value ∧
        ScopedDemandLeaf env root func types upper value := by
  classical
  simp [scopedDemandLeaves]

theorem ScopedDemandLeaf.origin {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {value : ValueId}
    (leaf : ScopedDemandLeaf env root func types upper value) :
    ScopedOriginLeaf env root func types upper value := by
  exact leaf.elim Or.inl (fun load => .inr (.inl load))

theorem ScopedOrigin.call_nonleaf_carrier {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {first last value : ValueId}
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup)
    {block : GIR.Block} (member : block ∈ func.blocks.toList)
    {function : FnId} {arguments : List ValueId} {origin : Option OriginId}
    (called : Inst.def value (.call function arguments origin) ∈ block.insts)
    (chosen : ScopedOrigin env root func types upper first last value)
    (notLeaf : ¬ ScopedDemandLeaf env root func types upper value) :
    ∃ type, types[value]? = some (some type) ∧ SliceViewType type := by
  classical
  rcases chosen.2.2 with carrier | ⟨mutability, payload, typeAt, consumed, _⟩
  · exact carrier
  · by_cases backed : ScopedTypedBacking func types value
    · obtain ⟨source, op, other, otherMember, defined, backing, _⟩ := backed
      have same := unique_definition_op unique member called otherMember defined
      subst op
      exact False.elim (backing.noncall function arguments origin rfl)
    · exact False.elim (notLeaf (.inl ⟨mutability, payload, typeAt, consumed, backed⟩))

theorem forFunction_scoped_call_origin_apart {module : GIR.Module} {env : PEnv} {root : DemandNode}
    {func : Func} {types : Array (Option VTy)} {upper : Prov} {first last value : ValueId}
    {returned : List RootRef} {queries : ReplacementQueries} {owner : ValueId}
    (canonical : types = func.valueTypes module)
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup)
    (values : ValueTypeShapes types)
    (globals : ∀ (index : Nat) (type : Ty) (kind : VarKind),
      (module.tyEnv func).globals[index]? = some (type, kind) → type.isRefLike = false)
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
      ScopedDemandLeaf env root func types upper value →
      ∃ dependencies, ((replacementContentFlow module).forFunction func types).ownerDependencies value = some dependencies ∧
        ReplacementApart queries owner (some dependencies))
    (calls : ∀ states, (replacementContentFlow module).model = some states →
      ∀ final, ((replacementContentFlow module).forFunction func types).model = some final →
      ∀ block ∈ func.blocks.toList, ∀ value function arguments origin,
      Inst.def value (.call function arguments origin) ∈ block.insts →
      ScopedOrigin env root func types upper first last value →
      ¬ ScopedDemandLeaf env root func types upper value →
      ∀ current, current.ScopedValuesWithin (ScopedOrigin env root func types upper first last)
        (OwnerDependencyApart module func queries owner) → current.Extends final →
        ((callState module states func current function arguments).1).AtomsWithin
          (OwnerDependencyApart module func queries owner))
    (chosen : ScopedOrigin env root func types upper first last value)
    (known : ((replacementContentFlow module).forFunction func types).value value = some returned) :
    ∃ dependencies, ((replacementContentFlow module).forFunction func types).ownerDependencies value = some dependencies ∧
      ReplacementApart queries owner (some dependencies) := by
  classical
  let leafValues := scopedDemandLeaves env root func types upper first last
  have classified := ScopedOrigin.definitions unique values globals fields typing uses references
  apply forFunction_scoped_calls_apart
    (bounded := fun value chosen => Nat.lt_of_lt_of_le chosen.2.1 bounded)
    (separate := fun entry entryAt value chosen _ member =>
      Nat.not_lt_of_ge chosen.1 (entryBefore entry entryAt value member))
    (leaves := leafValues)
    (definitions := ?_) (incoming := ?_) (leafQueries := ?_) (by
      intro states statesAt final finalAt block member value function arguments origin defined selected notLeaf
      exact calls states statesAt final finalAt block member value function arguments origin defined selected
        (fun leaf => notLeaf (mem_scopedDemandLeaves.mpr ⟨selected.2.1, selected, leaf⟩))) chosen known
  · intro block member value op defined selected
    rcases classified block member value op defined selected with leaf | forward
    · rcases leaf with reference | load | ⟨other, function, arguments, origin, otherMember, called⟩
      · exact .inl (mem_scopedDemandLeaves.mpr ⟨selected.2.1, selected, .inl reference⟩)
      · exact .inl (mem_scopedDemandLeaves.mpr ⟨selected.2.1, selected, .inr load⟩)
      · have same := unique_definition_op unique member defined otherMember called
        exact .inr (.inl ⟨function, arguments, origin, same.symm⟩)
    · rw [← canonical]
      exact .inr (.inr forward)
  · intro value selected notLeaf source input
    have noOriginLeaf : ¬ ScopedOriginLeaf env root func types upper value := by
      intro leaf
      rcases leaf with reference | load | ⟨block, function, arguments, origin, member, called⟩
      · exact notLeaf (mem_scopedDemandLeaves.mpr ⟨selected.2.1, selected, .inl reference⟩)
      · exact notLeaf (mem_scopedDemandLeaves.mpr ⟨selected.2.1, selected, .inr load⟩)
      · exact allIncomingValues_absent_of_definition unique member called input
    exact ScopedOrigin.incoming unique typing selected noOriginLeaf input
      (incoming value selected.1 selected.2.1 source input)
  · intro value member
    have actual := mem_scopedDemandLeaves.mp member
    exact leaves value actual.2.1 actual.2.2

#print axioms ScopedOrigin.call_nonleaf_carrier
#print axioms forFunction_scoped_call_origin_apart

end Goose.Lower.Validation.ReplacementContentFlowSource
