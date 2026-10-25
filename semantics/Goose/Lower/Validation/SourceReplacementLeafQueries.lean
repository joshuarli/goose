import Goose.Lower.Validation.SourceReplacementConsumedApart
import Goose.Lower.Validation.SourceCallResultQueryBounds
import Goose.Lower.Validation.ReplacementSourceCapturedBounds

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem site_scoped_leaf_query_known_of_accepted {module : Core.Module}
    {contextIndex : ContextId} {context : Context} {impl : Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, impl, context, []⟩ (.block impl.body) []
      (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)
      (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    {value : ValueId}
    (chosen : ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
      (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))
      upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size value)
    (leaf : ScopedOriginLeaf site.localEnv (.expression site.source.site.source.rhs)
      (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper value) :
    ∃ roots, ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))).value value = some roots := by
  rcases leaf with ⟨mutability, payload, reference, _, _⟩ |
    ⟨block, address, member, defined⟩ | ⟨block, callee, args, callOrigin, member, defined⟩
  · obtain ⟨consumer, op, block, member, defined, _, _, accessed⟩ := chosen.reference_use reference
    have used : value ∈ (Inst.def consumer op).uses := by
      cases op <;> simp only [accessOperands] at accessed <;> first | exact accessed | contradiction
    exact accepted_context_factory_operand_value accepted contextAt implAt member defined used
  · obtain ⟨roots, known⟩ := accepted_context_factory_load_value_known accepted contextAt implAt member defined
    rw [replacementQueries_value _ _ _ _
      (lowerContext_canonical_definition_bounds module context impl block member value (.load address) defined)] at known
    exact ⟨roots, known⟩
  · obtain ⟨roots, known⟩ := accepted_context_factory_call_value_known accepted contextAt implAt member defined
    rw [replacementQueries_value _ _ _ _
      (lowerContext_canonical_definition_bounds module context impl block member value (.call callee args callOrigin) defined)] at known
    exact ⟨roots, known⟩

theorem site_global_scoped_leaf_query_known_of_accepted {module : Core.Module}
    {globalIndex : GlobalId} {global : Core.Global}
    (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[globalIndex]? = some global)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, Core.initImpl, Core.initContext, []⟩ (.expression global.init) []
      (lowerEnv module #[] [global.ty]) (cfg_globalState module global)
      (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    {value : ValueId}
    (chosen : ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
      (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))
      upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size value)
    (leaf : ScopedOriginLeaf site.localEnv (.expression site.source.site.source.rhs)
      (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper value) :
    ∃ roots, ((replacementContentFlow (lower module)).forFunction (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module))).value value = some roots := by
  rcases leaf with ⟨mutability, payload, reference, _, _⟩ |
    ⟨block, address, member, defined⟩ | ⟨block, callee, args, callOrigin, member, defined⟩
  · obtain ⟨consumer, op, block, member, defined, _, _, accessed⟩ := chosen.reference_use reference
    have used : value ∈ (Inst.def consumer op).uses := by
      cases op <;> simp only [accessOperands] at accessed <;> first | exact accessed | contradiction
    exact accepted_global_factory_operand_value accepted globalAt member defined used
  · obtain ⟨roots, known⟩ := accepted_global_factory_load_value_known accepted globalAt member defined
    rw [replacementQueries_value _ _ _ _
      (lowerGlobal_canonical_definition_bounds module global block member value (.load address) defined)] at known
    exact ⟨roots, known⟩
  · obtain ⟨roots, known⟩ := accepted_global_factory_call_value_known accepted globalAt member defined
    rw [replacementQueries_value _ _ _ _
      (lowerGlobal_canonical_definition_bounds module global block member value (.call callee args callOrigin) defined)] at known
    exact ⟨roots, known⟩

#print axioms site_global_scoped_leaf_query_known_of_accepted
#print axioms site_scoped_leaf_query_known_of_accepted

end Goose.Lower.Validation
