import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceSites
import Goose.Lower.Validation.ReplacementScopedEmission
import Goose.Lower.Validation.ReplacementScopedOrigins

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR

theorem SiteOccurrences.fresh_instruction_occurrences
    {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {state : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    {blockIndex position owner value : Nat} {origin : OriginId}
    (site : SiteOccurrences env root targets le state func types upper
      blockIndex position owner value origin)
    (blocks : func.blocks = finishBlocks state.blocks) (dense : state.DenseDefinitions)
    {block : GIR.Block} {result : ValueId} {op : Op}
    (member : block ∈ func.blocks.toList) (defined : Inst.def result op ∈ block.insts)
    (lower : site.source.site.source.site.cleared.vals.size ≤ result)
    (bounded : result < site.source.site.source.site.captured.vals.size) :
    InstructionOccurrences site.localEnv (.expression site.source.site.source.rhs)
      func types upper (.def result op) :=
  site.rhs.fresh_definition site.source.site.source.cleared_generated.dense
    site.source.site.source.captured_generated.dense dense site.source.site.source.captured_extension
    blocks member defined lower bounded

theorem SiteOccurrences.scoped_leaf_occurrence
    {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {state : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    {blockIndex position owner value : Nat} {origin : OriginId}
    (site : SiteOccurrences env root targets le state func types upper
      blockIndex position owner value origin)
    (blocks : func.blocks = finishBlocks state.blocks) (dense : state.DenseDefinitions)
    {leafValue : ValueId}
    (chosen : ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) func types upper
      site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size leafValue)
    (leaf : ScopedOriginLeaf site.localEnv (.expression site.source.site.source.rhs) func types upper leafValue) :
    (ConsumedReferenceOccurrence site.localEnv (.expression site.source.site.source.rhs)
      func types upper leafValue ∧ ¬ ScopedTypedBacking func types leafValue) ∨
    (∃ address, ReadOccurrence site.localEnv (.expression site.source.site.source.rhs)
      func upper leafValue address) ∨
    ∃ callee args callOrigin, CallOccurrence site.localEnv (.expression site.source.site.source.rhs)
      func upper leafValue callee args callOrigin := by
  rcases leaf with ⟨mutability, payload, reference, consumed, unbacked⟩ |
    ⟨block, address, member, defined⟩ | ⟨block, callee, args, callOrigin, member, defined⟩
  · exact .inl ⟨consumed, unbacked⟩
  · have occurrence := site.fresh_instruction_occurrences blocks dense member defined chosen.1 chosen.2.1
    exact .inr (.inl ⟨address, occurrence.2.1 leafValue address rfl chosen.reference⟩)
  · have occurrence := site.fresh_instruction_occurrences blocks dense member defined chosen.1 chosen.2.1
    exact .inr (.inr ⟨callee, args, callOrigin, occurrence.2.2.1 leafValue callee args callOrigin rfl⟩)

#print axioms SiteOccurrences.fresh_instruction_occurrences
#print axioms SiteOccurrences.scoped_leaf_occurrence

end Goose.Lower.Validation.ReplacementContentFlowSource
