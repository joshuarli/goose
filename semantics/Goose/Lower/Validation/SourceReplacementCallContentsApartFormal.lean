import Goose.Lower.Validation.SourceReplacementCallContentsApartBounds

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR Goose.Core.Sound SummaryPreservation ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem site_forwarded_content_atom_apart_of_accepted {module : Core.Module}
    {contextIndex : ContextId} {context : Context} {implementation : Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implementationAt : module.impls[context.impl]? = some implementation)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, implementation, context, []⟩ (.block implementation.body) []
      (lowerEnv module implementation.vars implementation.results.toList) (cfg_implState module implementation)
      (lowerContextAt module context implementation)
      ((lowerContextAt module context implementation).valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    (demand : ReplacementDemandContext module contextIndex site.source.site.source.sourcePath
      site.source.site.source.place site.source.site.source.rhs origin)
    (below : ProvenanceBelow
      ((lowerContextAt module context implementation).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context implementation).valueTypes (lower module)) (lower module).rootCount) upper)
    {index : Nat} {declared : List RootRef}
    (annotation : (lowerContextAt module context implementation).roots.contents.find? (·.1 == index) =
      some (index, declared))
    (used : index ∈ site.source.site.source.rhs.variables) :
    OwnerDependencyApart (lower module) (lowerContextAt module context implementation)
      (replacementQueries (lower module) (lowerContextAt module context implementation)
        ((lowerContextAt module context implementation).valueTypes (lower module))) owner (.contents index) := by
  have nativeMember : (index, declared) ∈ (lowerContextAt module context implementation).roots.contents.toList := by
    rw [← Array.find?_toList] at annotation
    exact List.mem_of_find?_eq_some annotation
  obtain ⟨parameter, parameterAt, contentsAt⟩ := AdmittedSourceCalls.lowerContextAt_content_row_source nativeMember
  have aligned := ((validate_modOk module accepted).impl context.impl implementation implementationAt
    |>.params index parameter parameterAt).1
  have sourceContents : (context.contentRoots.find? (·.1 == index)).map (·.2) = some declared := by
    simpa only [aligned] using contentsAt
  obtain ⟨target, targetAt, ownerKnown⟩ :=
    site_owner_query_of_accepted accepted contextAt implementationAt site demand below
  obtain ⟨active, alias, aliasAt, rootsEq, interior⟩ :=
    demand.forwarded_content_alias accepted contextAt implementationAt sourceContents
  have atomKnown : normalizeAtom (lowerContextAt module context implementation) (.contents index) =
      some (declared.flatMap (lowerContextAt module context implementation).expandParameterRoot) := by
    simp only [normalizeAtom, annotation, Option.map_some]
  have normalized := normalize_singleton_atom atomKnown
  have within : unionRoots [] (declared.flatMap (lowerContextAt module context implementation).expandParameterRoot) ⊆
      alias.roots.flatMap (lowerContextAt module context implementation).expandParameterRoot := by
    rw [rootsEq]
    intro root member
    exact ((unionRoots_mem_iff _ _ _).mp member).resolve_left (by simp)
  have apart := demand.rhs_alias_query_apart used active targetAt
    (site_owner_invalidates contextAt implementationAt site demand targetAt) aliasAt interior
    (lowerContextAt_parameterRoots_closed accepted contextAt implementationAt) ownerKnown
    ⟨_, rfl, within⟩
  exact normalized_atoms_apart normalized apart (.contents index) (by simp)

theorem site_forwarded_content_cells_apart_of_accepted {module : Core.Module}
    {contextIndex : ContextId} {context : Context} {implementation : Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implementationAt : module.impls[context.impl]? = some implementation)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, implementation, context, []⟩ (.block implementation.body) []
      (lowerEnv module implementation.vars implementation.results.toList) (cfg_implState module implementation)
      (lowerContextAt module context implementation)
      ((lowerContextAt module context implementation).valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    (demand : ReplacementDemandContext module contextIndex site.source.site.source.sourcePath
      site.source.site.source.place site.source.site.source.rhs origin)
    (below : ProvenanceBelow
      ((lowerContextAt module context implementation).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context implementation).valueTypes (lower module)) (lower module).rootCount) upper)
    {final current : State}
    (finalAt : ((replacementContentFlow (lower module)).forFunction
      (lowerContextAt module context implementation)
      ((lowerContextAt module context implementation).valueTypes (lower module))).model = some final)
    (growth : current.Extends final)
    {index : Nat} {declared : List RootRef}
    (annotation : (lowerContextAt module context implementation).roots.contents.find? (·.1 == index) =
      some (index, declared))
    (used : index ∈ site.source.site.source.rhs.variables) :
    (flowAt current.contents index).AtomsWithin
      (OwnerDependencyApart (lower module) (lowerContextAt module context implementation)
        (replacementQueries (lower module) (lowerContextAt module context implementation)
          ((lowerContextAt module context implementation).valueTypes (lower module))) owner) := by
  have native := lowerContext_canonical_facts_of_accepted accepted contextAt implementationAt
  obtain ⟨annotations, entries, addresses⟩ := lower_canonical_factory_structure_of_accepted accepted
  have canonical := ReplacementContentFlow.forFunction_canonicalWithin native
    (lower_canonical_facts_of_accepted accepted) annotations entries addresses finalAt
  have nativeMember : (index, declared) ∈ (lowerContextAt module context implementation).roots.contents.toList := by
    rw [← Array.find?_toList] at annotation
    exact List.mem_of_find?_eq_some annotation
  obtain ⟨parameter, parameterAt, contentsAt⟩ := AdmittedSourceCalls.lowerContextAt_content_row_source nativeMember
  have aligned := ((validate_modOk module accepted).impl context.impl implementation implementationAt
    |>.params index parameter parameterAt).1
  have sourceContents : (context.contentRoots.find? (·.1 == index)).map (·.2) = some declared := by
    simpa only [aligned] using contentsAt
  have stateBound : index < final.contents.size := by
    rw [canonical.shape.contents]
    simpa only [lowerContextAt, lowerImpl, lowerImplFromState, List.length_map, Array.length_toList]
      using (Array.getElem?_eq_some_iff.mp parameterAt).1
  have refined := canonical.memory.contents index stateBound (by simp [annotation])
  rw [contentRoots_find native.roots.unique index, annotation] at refined
  simp only [Option.map_some, Option.getD_some] at refined
  apply (growth.contents.values index).atomsWithin
  change (flowAt final.contents index).AtomsWithin _
  by_cases pending : flowAt final.contents index = .pending
  · simp only [pending, Roots.AtomsWithin]
  · obtain ⟨actual, known, within⟩ := refined.actual native.roots.closed pending
    obtain ⟨target, targetAt, ownerKnown⟩ :=
      site_owner_query_of_accepted accepted contextAt implementationAt site demand below
    obtain ⟨active, alias, aliasAt, rootsEq, interior⟩ :=
      demand.forwarded_content_alias accepted contextAt implementationAt sourceContents
    apply normalized_atoms_apart known
    apply demand.rhs_alias_query_apart used active targetAt
      (site_owner_invalidates contextAt implementationAt site demand targetAt) aliasAt interior
      (lowerContextAt_parameterRoots_closed accepted contextAt implementationAt) ownerKnown
    exact ⟨actual, rfl, by simpa only [rootsEq] using within⟩

#print axioms site_forwarded_content_atom_apart_of_accepted
#print axioms site_forwarded_content_cells_apart_of_accepted

end Goose.Lower.Validation
