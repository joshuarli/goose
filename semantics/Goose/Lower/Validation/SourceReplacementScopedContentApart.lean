import Goose.Lower.Validation.SourceReplacementLeafQueries
import Goose.Lower.Validation.ReplacementScopedContentOrigins

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem site_scoped_content_atoms_of_accepted_leaves {module : Core.Module}
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
    {slots contents : Nat → Prop} {final : State}
    (initial : (start (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))).ScopedMemoryWithin slots contents
      (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner))
    (calls : ∀ states, (replacementContentFlow (lower module)).model = some states →
      ∀ final, ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))).model = some final →
      ∀ block ∈ (lowerContextAt module context impl).blocks.toList, ∀ value function arguments origin,
      Inst.def value (.call function arguments origin) ∈ block.insts →
      ∀ (current : State), current.ScopedContentWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) slots contents (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner) →
        current.Extends final →
        ((ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) value → ¬ ScopedDemandLeaf site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper value →
          ((callState (lower module) states (lowerContextAt module context impl) current function arguments).1).AtomsWithin
            (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner)) ∧
        ((callState (lower module) states (lowerContextAt module context impl) current function arguments).2).ScopedMemoryWithin slots contents
          (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner))
    (initializations : ∀ final, ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))).model = some final →
      ∀ block ∈ (lowerContextAt module context impl).blocks.toList, ∀ slot value origin, Inst.eff (.slotInit slot value origin) ∈ block.insts →
      ∀ (current : State), current.ScopedContentWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) slots contents (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner) →
        current.Extends final → slots slot → (flowAt current.values value).AtomsWithin
          (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner))
    (stores : ∀ final, ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))).model = some final →
      ∀ block ∈ (lowerContextAt module context impl).blocks.toList, ∀ address value origin, Inst.eff (.store address value origin) ∈ block.insts →
      ∀ (current : State), current.ScopedContentWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) slots contents (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner) →
        current.Extends final → valRefLike ((lowerContextAt module context impl).valueTypes (lower module)) value = true →
        (write (lowerContextAt module context impl) (touchValues ((lowerContextAt module context impl).valueTypes (lower module)) current [address]) (flowAt current.values address)
          (flowAt current.values value)).ScopedMemoryWithin slots contents (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner))
    (finalAt : ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))).model = some final) :
    final.ScopedContentWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) slots contents (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner) := by
  have facts := lowerContext_canonical_facts_of_accepted accepted contextAt implAt
  have dense := (dense_cfg_implAction impl (lowerEnv module impl.vars impl.results.toList) initState
    _ _ rfl LS.denseDefinitions_initState liveBound_initState).1
  have bound := site.source.site.source.captured_numValues_le (cfg_context_blocks module context impl) dense
  have graph := site.source.site.source.scoped_graph_inputs (cfg_context_blocks module context impl)
    site.clearedOperandUses (lowerContextAt_operand_bounds module context impl).2 dense
  have references : ∀ block ∈ (lowerContextAt module context impl).blocks.toList, ∀ result op,
      Inst.def result op ∈ block.insts → site.source.site.source.site.cleared.vals.size ≤ result →
      result < site.source.site.source.site.captured.vals.size → ∀ source ∈ accessOperands (.def result op),
      ∀ mutability payload, ((lowerContextAt module context impl).valueTypes (lower module))[source]? =
        some (some (.data (.ref mutability payload))) →
      ConsumedReferenceOccurrence site.localEnv (.expression site.source.site.source.rhs)
        (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper source := by
    intro block member result op defined lower bounded source accessed mutability payload reference
    exact (site.fresh_instruction_occurrences (cfg_context_blocks module context impl) dense
      member defined lower bounded).2.2.2.2 source accessed mutability payload reference
  have actualLeaves : ∀ leafValue,
      ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
        (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))
        upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size leafValue →
      ScopedDemandLeaf site.localEnv (.expression site.source.site.source.rhs)
        (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper leafValue →
      ∃ dependencies, ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))).ownerDependencies leafValue = some dependencies ∧
        ReplacementApart (replacementQueries (lower module) (lowerContextAt module context impl)
          ((lowerContextAt module context impl).valueTypes (lower module))) owner (some dependencies) := by
    intro leafValue selected leaf
    obtain ⟨roots, valueAt⟩ := site_scoped_leaf_query_known_of_accepted accepted contextAt implAt site selected leaf.origin
    obtain ⟨dependencies, dependencyAt, _⟩ := ReplacementFunctionFlow.ownerDependencies_of_value valueAt
    have apart : ReplacementApart (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner
        ((replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))).ownerDependencies leafValue) := by
      rcases leaf with ⟨mutability, payload, reference, occurrence, unbacked⟩ |
        ⟨block, address, member, defined⟩
      · exact site_unbacked_reference_apart_of_accepted accepted contextAt implAt site demand below selected reference occurrence unbacked
      · have apart := site_fresh_load_apart_of_accepted accepted contextAt implAt site demand below
          member defined selected.1 selected.2.1 selected.reference
        exact apart.loaded leafValue (by simp [loadedResults]) selected.reference
    rw [replacementQueries_ownerDependencies _ _ _ _ (Nat.lt_of_lt_of_le selected.2.1 bound), dependencyAt] at apart
    exact ⟨dependencies, dependencyAt, apart⟩
  exact forFunction_scoped_content_origin_atoms
    (module := lower module) (env := site.localEnv) (root := .expression site.source.site.source.rhs)
    (func := lowerContextAt module context impl)
    (types := (lowerContextAt module context impl).valueTypes (lower module)) (upper := upper)
    (first := site.source.site.source.site.cleared.vals.size)
    (last := site.source.site.source.site.captured.vals.size)
    (queries := replacementQueries (lower module) (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))) (owner := owner) rfl
    ((lowerImpl_dense_definitions module impl).nodup_iff.mpr List.nodup_range)
    facts.valuesShape facts.globalStorage facts.fields facts.typing graph.2.1 references graph.1 graph.2.2 bound
    actualLeaves initial calls initializations stores finalAt

theorem site_global_scoped_content_atoms_of_accepted_leaves {module : Core.Module}
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
    {slots contents : Nat → Prop} {final : State}
    (initial : (start (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))).ScopedMemoryWithin slots contents
      (OwnerDependencyApart (lower module) (lowerGlobal module global).init (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner))
    (calls : ∀ states, (replacementContentFlow (lower module)).model = some states →
      ∀ final, ((replacementContentFlow (lower module)).forFunction (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))).model = some final →
      ∀ block ∈ (lowerGlobal module global).init.blocks.toList, ∀ value function arguments origin,
      Inst.def value (.call function arguments origin) ∈ block.insts →
      ∀ (current : State), current.ScopedContentWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) slots contents (OwnerDependencyApart (lower module) (lowerGlobal module global).init (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner) →
        current.Extends final →
        ((ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) value → ¬ ScopedDemandLeaf site.localEnv (.expression site.source.site.source.rhs) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper value →
          ((callState (lower module) states (lowerGlobal module global).init current function arguments).1).AtomsWithin
            (OwnerDependencyApart (lower module) (lowerGlobal module global).init (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner)) ∧
        ((callState (lower module) states (lowerGlobal module global).init current function arguments).2).ScopedMemoryWithin slots contents
          (OwnerDependencyApart (lower module) (lowerGlobal module global).init (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner))
    (initializations : ∀ final, ((replacementContentFlow (lower module)).forFunction (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))).model = some final →
      ∀ block ∈ (lowerGlobal module global).init.blocks.toList, ∀ slot value origin, Inst.eff (.slotInit slot value origin) ∈ block.insts →
      ∀ (current : State), current.ScopedContentWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) slots contents (OwnerDependencyApart (lower module) (lowerGlobal module global).init (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner) →
        current.Extends final → slots slot → (flowAt current.values value).AtomsWithin
          (OwnerDependencyApart (lower module) (lowerGlobal module global).init (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner))
    (stores : ∀ final, ((replacementContentFlow (lower module)).forFunction (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))).model = some final →
      ∀ block ∈ (lowerGlobal module global).init.blocks.toList, ∀ address value origin, Inst.eff (.store address value origin) ∈ block.insts →
      ∀ (current : State), current.ScopedContentWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) slots contents (OwnerDependencyApart (lower module) (lowerGlobal module global).init (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner) →
        current.Extends final → valRefLike ((lowerGlobal module global).init.valueTypes (lower module)) value = true →
        (write (lowerGlobal module global).init (touchValues ((lowerGlobal module global).init.valueTypes (lower module)) current [address]) (flowAt current.values address)
          (flowAt current.values value)).ScopedMemoryWithin slots contents (OwnerDependencyApart (lower module) (lowerGlobal module global).init (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner))
    (finalAt : ((replacementContentFlow (lower module)).forFunction (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))).model = some final) :
    final.ScopedContentWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) slots contents (OwnerDependencyApart (lower module) (lowerGlobal module global).init (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner) := by
  have facts := lowerGlobal_canonical_facts_of_accepted accepted globalAt
  have dense := cfg_globalState_denseDefinitions module global
  have bound := site.source.site.source.captured_numValues_le (cfg_global_blocks module global) dense
  have graph := site.source.site.source.scoped_graph_inputs (cfg_global_blocks module global)
    site.clearedOperandUses (lowerGlobal_operand_bounds module global).2 dense
  have references : ∀ block ∈ (lowerGlobal module global).init.blocks.toList, ∀ result op,
      Inst.def result op ∈ block.insts → site.source.site.source.site.cleared.vals.size ≤ result →
      result < site.source.site.source.site.captured.vals.size → ∀ source ∈ accessOperands (.def result op),
      ∀ mutability payload, ((lowerGlobal module global).init.valueTypes (lower module))[source]? =
        some (some (.data (.ref mutability payload))) →
      ConsumedReferenceOccurrence site.localEnv (.expression site.source.site.source.rhs)
        (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper source := by
    intro block member result op defined lower bounded source accessed mutability payload reference
    exact (site.fresh_instruction_occurrences (cfg_global_blocks module global) dense
      member defined lower bounded).2.2.2.2 source accessed mutability payload reference
  have actualLeaves : ∀ leafValue,
      ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
        (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))
        upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size leafValue →
      ScopedDemandLeaf site.localEnv (.expression site.source.site.source.rhs)
        (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper leafValue →
      ∃ dependencies, ((replacementContentFlow (lower module)).forFunction (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module))).ownerDependencies leafValue = some dependencies ∧
        ReplacementApart (replacementQueries (lower module) (lowerGlobal module global).init
          ((lowerGlobal module global).init.valueTypes (lower module))) owner (some dependencies) := by
    intro leafValue selected leaf
    obtain ⟨roots, valueAt⟩ := site_global_scoped_leaf_query_known_of_accepted accepted globalAt site selected leaf.origin
    obtain ⟨dependencies, dependencyAt, _⟩ := ReplacementFunctionFlow.ownerDependencies_of_value valueAt
    have apart : ReplacementApart (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner
        ((replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))).ownerDependencies leafValue) := by
      rcases leaf with ⟨mutability, payload, reference, occurrence, unbacked⟩ |
        ⟨block, address, member, defined⟩
      · exact site_global_unbacked_reference_apart_of_accepted accepted globalAt site demand below selected reference occurrence unbacked
      · have apart := site_fresh_global_load_apart_of_accepted accepted globalAt site demand below
          member defined selected.1 selected.2.1 selected.reference
        exact apart.loaded leafValue (by simp [loadedResults]) selected.reference
    rw [replacementQueries_ownerDependencies _ _ _ _ (Nat.lt_of_lt_of_le selected.2.1 bound), dependencyAt] at apart
    exact ⟨dependencies, dependencyAt, apart⟩
  exact forFunction_scoped_content_origin_atoms
    (module := lower module) (env := site.localEnv) (root := .expression site.source.site.source.rhs)
    (func := (lowerGlobal module global).init)
    (types := (lowerGlobal module global).init.valueTypes (lower module)) (upper := upper)
    (first := site.source.site.source.site.cleared.vals.size)
    (last := site.source.site.source.site.captured.vals.size)
    (queries := replacementQueries (lower module) (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module))) (owner := owner) rfl
    ((lowerGlobal_dense_definitions module global).nodup_iff.mpr List.nodup_range)
    facts.valuesShape facts.globalStorage facts.fields facts.typing graph.2.1 references graph.1 graph.2.2 bound
    actualLeaves initial calls initializations stores finalAt

#print axioms site_scoped_content_atoms_of_accepted_leaves
#print axioms site_global_scoped_content_atoms_of_accepted_leaves

end Goose.Lower.Validation
