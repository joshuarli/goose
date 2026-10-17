import Goose.Lower.Validation.ReplacementScopedCallOrigins
import Goose.Lower.Validation.ReplacementScopedContentApart

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR ReplacementContentFlow.Model

theorem forFunction_scoped_content_origin_atoms {module : GIR.Module} {env : PEnv} {root : DemandNode}
    {func : Func} {types : Array (Option VTy)} {upper : Prov} {first last : ValueId}
    {queries : ReplacementQueries} {owner : ValueId} {slots contents : Nat → Prop} {final : State}
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
    (initial : (start func (func.valueTypes module)).ScopedMemoryWithin slots contents
      (OwnerDependencyApart module func queries owner))
    (calls : ∀ states, (replacementContentFlow module).model = some states →
      ∀ final, ((replacementContentFlow module).forFunction func types).model = some final →
      ∀ block ∈ func.blocks.toList, ∀ value function arguments origin,
      Inst.def value (.call function arguments origin) ∈ block.insts →
      ∀ (current : State), current.ScopedContentWithin (ScopedOrigin env root func types upper first last) slots contents (OwnerDependencyApart module func queries owner) →
        current.Extends final →
        ((ScopedOrigin env root func types upper first last) value → ¬ ScopedDemandLeaf env root func types upper value →
          ((callState module states func current function arguments).1).AtomsWithin
            (OwnerDependencyApart module func queries owner)) ∧
        ((callState module states func current function arguments).2).ScopedMemoryWithin slots contents
          (OwnerDependencyApart module func queries owner))
    (initializations : ∀ final, ((replacementContentFlow module).forFunction func types).model = some final →
      ∀ block ∈ func.blocks.toList, ∀ slot value origin, Inst.eff (.slotInit slot value origin) ∈ block.insts →
      ∀ (current : State), current.ScopedContentWithin (ScopedOrigin env root func types upper first last) slots contents (OwnerDependencyApart module func queries owner) →
        current.Extends final → slots slot → (flowAt current.values value).AtomsWithin
          (OwnerDependencyApart module func queries owner))
    (stores : ∀ final, ((replacementContentFlow module).forFunction func types).model = some final →
      ∀ block ∈ func.blocks.toList, ∀ address value origin, Inst.eff (.store address value origin) ∈ block.insts →
      ∀ (current : State), current.ScopedContentWithin (ScopedOrigin env root func types upper first last) slots contents (OwnerDependencyApart module func queries owner) →
        current.Extends final → valRefLike (func.valueTypes module) value = true →
        (write func (touchValues (func.valueTypes module) current [address]) (flowAt current.values address)
          (flowAt current.values value)).ScopedMemoryWithin slots contents (OwnerDependencyApart module func queries owner))
    (finalAt : ((replacementContentFlow module).forFunction func types).model = some final) :
    final.ScopedContentWithin (ScopedOrigin env root func types upper first last) slots contents (OwnerDependencyApart module func queries owner) := by
  classical
  let leafValues := scopedDemandLeaves env root func types upper first last
  have classified := ScopedOrigin.definitions unique values globals fields typing uses references
  apply forFunction_scoped_content_atoms
    (bounded := fun value chosen => Nat.lt_of_lt_of_le chosen.2.1 bounded)
    (separate := fun entry entryAt value chosen _ member =>
      Nat.not_lt_of_ge chosen.1 (entryBefore entry entryAt value member))
    (leaves := leafValues)
    (definitions := ?_) (incoming := ?_) (leafQueries := ?_) initial ?_ initializations stores finalAt
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
  · intro states statesAt final finalAt block member value function arguments origin defined current within growth
    have output := calls states statesAt final finalAt block member value function arguments origin defined current within growth
    refine ⟨?_, output.2⟩
    intro chosen notLeaf
    exact output.1 chosen (fun leaf => notLeaf (mem_scopedDemandLeaves.mpr ⟨chosen.2.1, chosen, leaf⟩))

#print axioms forFunction_scoped_content_origin_atoms

end Goose.Lower.Validation.ReplacementContentFlowSource
