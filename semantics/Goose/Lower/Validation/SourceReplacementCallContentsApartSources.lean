import Goose.Lower.Validation.SourceReplacementCallContentsApart
import Goose.Lower.Validation.ReplacementSourceOperandBounds
import Goose.GIR.ReplacementContentFlowProofsScopedContent
import Goose.GIR.ReplacementContentFlowProofsScopedContentCalls

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem ReplacementContentFlowSource.SiteOccurrences.fresh_instruction_operand_bounds
    {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {state : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    {blockIndex sitePosition owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences env root targets le state func types upper
      blockIndex sitePosition owner replacementValue origin)
    (blocks : func.blocks = finishBlocks state.blocks)
    (ordered : ∀ block ∈ func.blocks.toList, ∀ value op,
      Inst.def value op ∈ block.insts → ∀ input ∈ op.uses, input < value)
    {index position : Nat} {body : BlockB} {instruction : Inst}
    (bodyAt : site.source.site.source.site.captured.blocks[index]? = some body)
    (instructionAt : body.insts.toList[position]? = some instruction)
    (location : site.source.site.source.site.cleared.blocks.size ≤ index ∨
      ∃ initial, site.source.site.source.site.cleared.blocks[index]? = some initial ∧
        initial.insts.size ≤ position) :
    ∀ value ∈ instruction.uses,
      site.source.site.source.site.cleared.vals.size ≤ value ∧
      value < site.source.site.source.site.captured.vals.size := by
  have emitted := lowerExpr_emitsFreshUses site.source.site.source.rhs
    site.source.site.source.site.rhsRun
  have fresh := emitted.instruction_after_prefix bodyAt instructionAt location
  have capturedBounds := operands_source_lowerExpr site.source.site.source.rhs _ _ _ _
    site.source.site.source.site.rhsRun (site.cleared_operandBounds blocks ordered)
  have member : instruction ∈ site.source.site.source.site.captured.insts := by
    apply List.mem_flatMap.mpr
    exact ⟨body, Array.mem_toList_iff.mpr (Array.mem_of_getElem? bodyAt),
      List.mem_of_getElem? instructionAt⟩
  intro value used
  exact ⟨fresh value used, capturedBounds.uses instruction member value used⟩

theorem ReplacementContentFlowSource.SiteOccurrences.fresh_slice_slotInit_source
    {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {state : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    {blockIndex sitePosition owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences env root targets le state func types upper
      blockIndex sitePosition owner replacementValue origin)
    (blocks : func.blocks = finishBlocks state.blocks)
    (ordered : ∀ block ∈ func.blocks.toList, ∀ value op,
      Inst.def value op ∈ block.insts → ∀ input ∈ op.uses, input < value)
    {index position slot source : Nat} {body : BlockB} {sourceOrigin : Option OriginId}
    (bodyAt : site.source.site.source.site.captured.blocks[index]? = some body)
    (instructionAt : body.insts.toList[position]? = some (.eff (.slotInit slot source sourceOrigin)))
    (location : site.source.site.source.site.cleared.blocks.size ≤ index ∨
      ∃ initial, site.source.site.source.site.cleared.blocks[index]? = some initial ∧
        initial.insts.size ≤ position)
    {mutability : Mutability} {element : Ty}
    (typed : types[source]? = some (some (.data (.slice mutability element)))) :
    ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) func types upper
      site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size source := by
  have bounded := site.fresh_instruction_operand_bounds blocks ordered bodyAt instructionAt location source
    (by simp [Inst.uses, Effect.uses])
  exact ⟨bounded.1, bounded.2, .inl ⟨.data (.slice mutability element), typed, .slice mutability element⟩⟩

theorem ReplacementContentFlowSource.SiteOccurrences.fresh_slice_store_source
    {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {state : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    {blockIndex sitePosition owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences env root targets le state func types upper
      blockIndex sitePosition owner replacementValue origin)
    (blocks : func.blocks = finishBlocks state.blocks)
    (ordered : ∀ block ∈ func.blocks.toList, ∀ value op,
      Inst.def value op ∈ block.insts → ∀ input ∈ op.uses, input < value)
    {index position address source : Nat} {body : BlockB} {sourceOrigin : Option OriginId}
    (bodyAt : site.source.site.source.site.captured.blocks[index]? = some body)
    (instructionAt : body.insts.toList[position]? = some (.eff (.store address source sourceOrigin)))
    (location : site.source.site.source.site.cleared.blocks.size ≤ index ∨
      ∃ initial, site.source.site.source.site.cleared.blocks[index]? = some initial ∧
        initial.insts.size ≤ position)
    {mutability : Mutability} {element : Ty}
    (typed : types[source]? = some (some (.data (.slice mutability element)))) :
    ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) func types upper
      site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size source := by
  have bounded := site.fresh_instruction_operand_bounds blocks ordered bodyAt instructionAt location source
    (by simp [Inst.uses, Effect.uses])
  exact ⟨bounded.1, bounded.2, .inl ⟨.data (.slice mutability element), typed, .slice mutability element⟩⟩

theorem canonical_scoped_content_atoms
    {func : Func} {types : Array (Option VTy)}
    {provenance upper : Prov} {current final : State} {argument : ValueId}
    {mutability : Mutability} {payload : Ty} {predicate : Atom → Prop}
    (canonical : final.CanonicalWithin func types provenance)
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    (bounded : argument < final.values.size)
    (native : types[argument]? = some (some (.data (.ref mutability payload))))
    (reference : payload.isRefLike = true)
    (below : rootsAt provenance.vals argument ⊆ rootsAt upper.vals argument)
    (growth : current.Extends final)
    (memory : current.ScopedMemoryWithin
      (fun slot => RootRef.local slot ∈ rootsAt upper.vals argument)
      (fun index => RootRef.param index ∈ rootsAt upper.vals argument) predicate) :
    (content func current (flowAt current.values argument)).AtomsWithin predicate := by
  have finalHolder := canonical.holderValues argument bounded mutability payload native reference
  have currentHolder : HolderRoots func payload (rootsAt provenance.vals argument)
      (flowAt current.values argument) := (growth.values.values argument).atomsWithin finalHolder
  exact memory.read currentHolder parameters reference
    (fun slot storage row type member => below member)
    (fun index mutability row member => below member)

#print axioms ReplacementContentFlowSource.SiteOccurrences.fresh_instruction_operand_bounds
#print axioms ReplacementContentFlowSource.SiteOccurrences.fresh_slice_slotInit_source
#print axioms ReplacementContentFlowSource.SiteOccurrences.fresh_slice_store_source
#print axioms canonical_scoped_content_atoms

end Goose.Lower.Validation
