import Goose.Lower.Validation.SourceReplacementScopedCallApart
import Goose.Lower.Validation.SourceScalarQueries

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem site_current_call_arguments_apart {module : Core.Module}
    {contextIndex : ContextId} {context : Context} {impl : Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, impl, context, []⟩ (.block impl.body) []
      (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)
      (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    {value function : ValueId} {arguments : List ValueId} {callOrigin : Option OriginId} {block : GIR.Block}
    (member : block ∈ (lowerContextAt module context impl).blocks.toList)
    (called : Inst.def value (.call function arguments callOrigin) ∈ block.insts)
    (fresh : site.source.site.source.site.cleared.vals.size ≤ value ∧ value < site.source.site.source.site.captured.vals.size)
    {current final : State}
    (finalAt : ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))).model = some final)
    (below : current.Extends final)
    (within : current.ScopedValuesWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner)) :
    ∀ argument ∈ arguments, (flowAt current.values argument).AtomsWithin (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner) := by
  have facts := lowerContext_canonical_facts_of_accepted accepted contextAt implAt
  have dense := (dense_cfg_implAction impl (lowerEnv module impl.vars impl.results.toList) initState
    _ _ rfl LS.denseDefinitions_initState liveBound_initState).1
  have bound := site.source.site.source.captured_numValues_le (cfg_context_blocks module context impl) dense
  have graph := site.source.site.source.scoped_graph_inputs (cfg_context_blocks module context impl)
    site.clearedOperandUses (lowerContextAt_operand_bounds module context impl).2 dense
  have occurrence := site.fresh_instruction_occurrences (cfg_context_blocks module context impl) dense
    member called fresh.1 fresh.2
  have shape := function_model_shape finalAt
  have scalars := function_model_scalar_values facts.typing finalAt
  intro argument argumentMember
  by_cases reference : valRefLike ((lowerContextAt module context impl).valueTypes (lower module)) argument = true
  · have bounds := graph.2.1 block member value (.call function arguments callOrigin) called
      fresh.1 fresh.2 argument argumentMember
    obtain ⟨type, typeAt, carrier | ⟨mutability, payload, same⟩⟩ := valRefLike_type_cases reference
    · exact within argument ⟨bounds.1, bounds.2, .inl ⟨type, typeAt, carrier⟩⟩
    · subst type
      apply within argument
      refine ⟨bounds.1, bounds.2, .inr ⟨mutability, payload, typeAt, ?_, ?_⟩⟩
      · exact occurrence.2.2.2.2 argument argumentMember mutability payload typeAt
      · exact ⟨value, .call function arguments callOrigin, block, member, called,
          fresh.1, fresh.2, argumentMember⟩
  · have scalar : valRefLike ((lowerContextAt module context impl).valueTypes (lower module)) argument = false := Bool.eq_false_iff.mpr reference
    have bounded := (lowerContextAt_operand_bounds module context impl).1 block member
      (.def value (.call function arguments callOrigin)) called argument argumentMember
    exact (below.values.values argument).atomsWithin
      ((scalars argument (shape.values ▸ bounded) scalar).mono (fun atom impossible => False.elim impossible))

theorem site_global_current_call_arguments_apart {module : Core.Module}
    {globalIndex : GlobalId} {global : Core.Global}
    (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[globalIndex]? = some global)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, Core.initImpl, Core.initContext, []⟩ (.expression global.init) []
      (lowerEnv module #[] [global.ty]) (cfg_globalState module global)
      (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    {value function : ValueId} {arguments : List ValueId} {callOrigin : Option OriginId} {block : GIR.Block}
    (member : block ∈ (lowerGlobal module global).init.blocks.toList)
    (called : Inst.def value (.call function arguments callOrigin) ∈ block.insts)
    (fresh : site.source.site.source.site.cleared.vals.size ≤ value ∧ value < site.source.site.source.site.captured.vals.size)
    {current final : State}
    (finalAt : ((replacementContentFlow (lower module)).forFunction (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))).model = some final)
    (below : current.Extends final)
    (within : current.ScopedValuesWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) (OwnerDependencyApart (lower module) (lowerGlobal module global).init (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner)) :
    ∀ argument ∈ arguments, (flowAt current.values argument).AtomsWithin (OwnerDependencyApart (lower module) (lowerGlobal module global).init (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner) := by
  have facts := lowerGlobal_canonical_facts_of_accepted accepted globalAt
  have dense := cfg_globalState_denseDefinitions module global
  have bound := site.source.site.source.captured_numValues_le (cfg_global_blocks module global) dense
  have graph := site.source.site.source.scoped_graph_inputs (cfg_global_blocks module global)
    site.clearedOperandUses (lowerGlobal_operand_bounds module global).2 dense
  have occurrence := site.fresh_instruction_occurrences (cfg_global_blocks module global) dense
    member called fresh.1 fresh.2
  have shape := function_model_shape finalAt
  have scalars := function_model_scalar_values facts.typing finalAt
  intro argument argumentMember
  by_cases reference : valRefLike ((lowerGlobal module global).init.valueTypes (lower module)) argument = true
  · have bounds := graph.2.1 block member value (.call function arguments callOrigin) called
      fresh.1 fresh.2 argument argumentMember
    obtain ⟨type, typeAt, carrier | ⟨mutability, payload, same⟩⟩ := valRefLike_type_cases reference
    · exact within argument ⟨bounds.1, bounds.2, .inl ⟨type, typeAt, carrier⟩⟩
    · subst type
      apply within argument
      refine ⟨bounds.1, bounds.2, .inr ⟨mutability, payload, typeAt, ?_, ?_⟩⟩
      · exact occurrence.2.2.2.2 argument argumentMember mutability payload typeAt
      · exact ⟨value, .call function arguments callOrigin, block, member, called,
          fresh.1, fresh.2, argumentMember⟩
  · have scalar : valRefLike ((lowerGlobal module global).init.valueTypes (lower module)) argument = false := Bool.eq_false_iff.mpr reference
    have bounded := (lowerGlobal_operand_bounds module global).1 block member
      (.def value (.call function arguments callOrigin)) called argument argumentMember
    exact (below.values.values argument).atomsWithin
      ((scalars argument (shape.values ▸ bounded) scalar).mono (fun atom impossible => False.elim impossible))

#print axioms site_current_call_arguments_apart
#print axioms site_global_current_call_arguments_apart

end Goose.Lower.Validation
