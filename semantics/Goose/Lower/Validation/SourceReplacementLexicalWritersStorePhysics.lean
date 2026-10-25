import Goose.Lower.Validation.SourceReadyInductionFacts

namespace Goose.Lower.Validation.SourceReplacementLexicalWriters

open Goose.Core Goose.GIR ReplacementContentFlowSource

theorem store_tracked_local_upper (facts : SourceReadyFunction)
    {block : GIR.Block} (blockMember : block ∈ facts.func.blocks.toList)
    {address value : ValueId} {origin : Option OriginId}
    (instMember : Inst.eff (.store address value origin) ∈ block.insts)
    (reference : valRefLike facts.types value = true)
    {tracked : VarId} (trackedMember : RootRef.local tracked ∈ rootsAt facts.provenance.vals address) :
    rootsAt facts.upper.vals address = [.local tracked] := by
  have occurrence := (facts.occurrences block blockMember _ instMember).2.2.2.1 address value origin rfl reference
  rcases occurrence with assignment | rebind
  · obtain ⟨assignment⟩ := assignment
    obtain ⟨parameter, place, formal⟩ := assignment.referenceTarget
    have impossible := assignment.formalAddress parameter place formal (facts.below address trackedMember)
    simp at impossible
  · obtain ⟨rebind⟩ := rebind
    have member := facts.below address trackedMember
    rw [rebind.addressRoots] at member
    have same : tracked = rebind.varId := by simpa using member
    simpa only [same] using rebind.addressRoots

#print axioms store_tracked_local_upper

end Goose.Lower.Validation.SourceReplacementLexicalWriters
