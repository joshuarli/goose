import Goose.Lower.Validation.SourceReplacementSourceOperandsApart
import Goose.Lower.Validation.ReplacementEmissionIntersection

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

private theorem accessOperand_used {instruction : Inst} {value : ValueId}
    (member : value ∈ accessOperands instruction) : value ∈ instruction.uses := by
  cases instruction with
  | «def» result op =>
    cases op <;> simp only [accessOperands] at member <;> first | exact member | contradiction
  | eff effect =>
    cases effect <;> simp only [accessOperands] at member <;> first
      | exact member
      | contradiction
      | exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp member))
  | term term => simp [accessOperands] at member

private theorem emptyFactSourceOperand_access {instruction : Inst} {value : ValueId}
    (member : value ∈ emptyFactSourceOperands instruction) : value ∈ accessOperands instruction := by
  cases instruction with
  | eff effect => cases effect <;> simp_all [emptyFactSourceOperands, accessOperands]
  | «def» result op => exact member
  | term term => exact member

private theorem loadedResult_site {instruction : Inst} {value : ValueId}
    (member : value ∈ loadedResults instruction) : ∃ address, instruction = .def value (.load address) := by
  cases instruction with
  | «def» result op =>
    cases op <;> simp only [loadedResults, List.not_mem_nil] at member
    case load address =>
      have same : value = result := List.mem_singleton.mp member
      subst result
      exact ⟨address, rfl⟩
  | eff effect => simp [loadedResults] at member
  | term term => simp [loadedResults] at member

theorem site_rhs_apart_of_calls {module : Core.Module}
    {contextIndex : ContextId} {context : Context} {impl : Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, impl, context, []⟩ (.block impl.body) []
      (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)
      (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    (demand : ReplacementDemandContext module contextIndex
      site.source.site.source.sourcePath site.source.site.source.place site.source.site.source.rhs origin)
    (below : ProvenanceBelow
      ((lowerContextAt module context impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount) upper)
    (calls : ∀ value block callee args callOrigin,
      block ∈ (lowerContextAt module context impl).blocks.toList →
      Inst.def value (.call callee args callOrigin) ∈ block.insts →
      ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
        (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))
        upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size value →
      ReplacementApart (replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))) owner
        ((replacementQueries (lower module) (lowerContextAt module context impl)
          ((lowerContextAt module context impl).valueTypes (lower module))).ownerDependencies value))
    (callEffects : ∀ value block callee args callOrigin,
      block ∈ (lowerContextAt module context impl).blocks.toList →
      Inst.def value (.call callee args callOrigin) ∈ block.insts →
      CallOccurrence site.localEnv (.expression site.source.site.source.rhs)
        (lowerContextAt module context impl) upper value callee args callOrigin →
      ReplacementApart (replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))) owner
        (callDependencies (lower module) ((lowerContextAt module context impl).valueTypes (lower module))
          (replacementQueries (lower module) (lowerContextAt module context impl)
            ((lowerContextAt module context impl).valueTypes (lower module))) callee args)) :
    EmitsOnly (ReplacementInstApart (lower module) ((lowerContextAt module context impl).valueTypes (lower module))
      (replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))) owner)
      site.source.site.source.site.cleared site.source.site.source.site.captured := by
  have fresh := lowerExpr_emitsFreshUses site.source.site.source.rhs site.source.site.source.site.rhsRun
  have operandBounds := operands_source_lowerExpr site.source.site.source.rhs _ _ _ _
    site.source.site.source.site.rhsRun site.context_cleared_operandBounds
  apply (site.rhs.inter fresh).map
  intro instruction capturedMember evidence
  obtain ⟨block, member, instructionMember⟩ := finished_instruction_of_extension
    site.source.site.source.captured_extension (cfg_context_blocks module context impl) capturedMember
  obtain ⟨occurrences, freshUses⟩ := evidence
  constructor
  · intro value sourceMember reference
    have accessed := emptyFactSourceOperand_access sourceMember
    have used := accessOperand_used accessed
    have lowerBound := freshUses value used
    have upperBound := operandBounds.uses instruction capturedMember value used
    obtain ⟨type, typeAt, shape⟩ := valRefLike_type_cases reference
    rcases shape with carrier | ⟨mutability, payload, same⟩
    · have chosen : ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
          (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper
          site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size value :=
        ⟨lowerBound, upperBound, Or.inl ⟨type, typeAt, carrier⟩⟩
      obtain ⟨roots, known⟩ := accepted_context_factory_operand_value accepted contextAt implAt
        member instructionMember used
      exact site_scoped_origin_apart_of_leaves accepted contextAt implAt site
        (fun leafValue selected leaf => site_scoped_leaf_apart_of_calls accepted contextAt implAt site demand below
          calls selected leaf) chosen known
    · subst type
      exact site_consumed_reference_apart_of_calls accepted contextAt implAt site demand below calls
        member instructionMember used lowerBound upperBound typeAt
        (occurrences.2.2.2.2 value accessed mutability payload typeAt)
  · intro value loaded reference
    obtain ⟨address, same⟩ := loadedResult_site loaded
    subst instruction
    have occurrence := occurrences.2.1 value address rfl reference
    exact (site_load_apart_of_accepted accepted contextAt implAt site demand below member instructionMember
      occurrence).loaded value (by simp [loadedResults]) reference
  · intro value callee args callOrigin same
    subst instruction
    exact callEffects value block callee args callOrigin member instructionMember
      (occurrences.2.2.1 value callee args callOrigin rfl)

theorem site_global_rhs_apart_of_calls {module : Core.Module}
    {globalIndex : GlobalId} {global : Core.Global}
    (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[globalIndex]? = some global)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, Core.initImpl, Core.initContext, []⟩ (.expression global.init) []
      (lowerEnv module #[] [global.ty]) (cfg_globalState module global)
      (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    (demand : ReplacementDemandContext module (module.contexts.size + globalIndex)
      site.source.site.source.sourcePath site.source.site.source.place site.source.site.source.rhs origin)
    (below : ProvenanceBelow
      ((lowerGlobal module global).init.provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount) upper)
    (calls : ∀ value block callee args callOrigin,
      block ∈ (lowerGlobal module global).init.blocks.toList →
      Inst.def value (.call callee args callOrigin) ∈ block.insts →
      ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
        (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))
        upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size value →
      ReplacementApart (replacementQueries (lower module) (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module))) owner
        ((replacementQueries (lower module) (lowerGlobal module global).init
          ((lowerGlobal module global).init.valueTypes (lower module))).ownerDependencies value))
    (callEffects : ∀ value block callee args callOrigin,
      block ∈ (lowerGlobal module global).init.blocks.toList →
      Inst.def value (.call callee args callOrigin) ∈ block.insts →
      CallOccurrence site.localEnv (.expression site.source.site.source.rhs)
        (lowerGlobal module global).init upper value callee args callOrigin →
      ReplacementApart (replacementQueries (lower module) (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module))) owner
        (callDependencies (lower module) ((lowerGlobal module global).init.valueTypes (lower module))
          (replacementQueries (lower module) (lowerGlobal module global).init
            ((lowerGlobal module global).init.valueTypes (lower module))) callee args)) :
    EmitsOnly (ReplacementInstApart (lower module) ((lowerGlobal module global).init.valueTypes (lower module))
      (replacementQueries (lower module) (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module))) owner)
      site.source.site.source.site.cleared site.source.site.source.site.captured := by
  have fresh := lowerExpr_emitsFreshUses site.source.site.source.rhs site.source.site.source.site.rhsRun
  have operandBounds := operands_source_lowerExpr site.source.site.source.rhs _ _ _ _
    site.source.site.source.site.rhsRun site.global_cleared_operandBounds
  apply (site.rhs.inter fresh).map
  intro instruction capturedMember evidence
  obtain ⟨block, member, instructionMember⟩ := finished_instruction_of_extension
    site.source.site.source.captured_extension (cfg_global_blocks module global) capturedMember
  obtain ⟨occurrences, freshUses⟩ := evidence
  constructor
  · intro value sourceMember reference
    have accessed := emptyFactSourceOperand_access sourceMember
    have used := accessOperand_used accessed
    have lowerBound := freshUses value used
    have upperBound := operandBounds.uses instruction capturedMember value used
    obtain ⟨type, typeAt, shape⟩ := valRefLike_type_cases reference
    rcases shape with carrier | ⟨mutability, payload, same⟩
    · have chosen : ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
          (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper
          site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size value :=
        ⟨lowerBound, upperBound, Or.inl ⟨type, typeAt, carrier⟩⟩
      obtain ⟨roots, known⟩ := accepted_global_factory_operand_value accepted globalAt
        member instructionMember used
      exact site_global_scoped_origin_apart_of_leaves accepted globalAt site
        (fun leafValue selected leaf => site_global_scoped_leaf_apart_of_calls accepted globalAt site demand below
          calls selected leaf) chosen known
    · subst type
      exact site_global_consumed_reference_apart_of_calls accepted globalAt site demand below calls
        member instructionMember used lowerBound upperBound typeAt
        (occurrences.2.2.2.2 value accessed mutability payload typeAt)
  · intro value loaded reference
    obtain ⟨address, same⟩ := loadedResult_site loaded
    subst instruction
    have occurrence := occurrences.2.1 value address rfl reference
    exact (site_global_load_apart_of_accepted accepted globalAt site demand below member instructionMember
      occurrence).loaded value (by simp [loadedResults]) reference
  · intro value callee args callOrigin same
    subst instruction
    exact callEffects value block callee args callOrigin member instructionMember
      (occurrences.2.2.1 value callee args callOrigin rfl)

#print axioms site_global_rhs_apart_of_calls
#print axioms site_rhs_apart_of_calls

end Goose.Lower.Validation
