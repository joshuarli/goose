import Goose.Lower.Validation.SourceCanonicalFactsAssembly
import Goose.Lower.Validation.ReplacementCanonicalQueryBounds

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR Goose.GIR.ReplacementContentFlow.Model

theorem lowerContext_factory_value_within_provenance_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : ContextId} {context : Context} {impl : Impl}
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {value : ValueId} {roots : List RootRef}
    (known : ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))).value value = some roots) :
    roots ⊆ (rootsAt ((lowerContextAt module context impl).provenance
      (resultRoots (lower module) (lower module).implTypes)
      ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount).vals value).flatMap
        (lowerContextAt module context impl).expandParameterRoot := by
  obtain ⟨annotations, entries, addresses⟩ := lower_canonical_factory_structure_of_accepted accepted
  exact ReplacementContentFlow.forFunction_value_within_provenance
    (lowerContext_canonical_facts_of_accepted accepted contextAt implAt)
    (lower_canonical_facts_of_accepted accepted) annotations entries addresses known

theorem lowerGlobal_factory_value_within_provenance_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : GlobalId} {global : Core.Global}
    (globalAt : module.globals[index]? = some global)
    {value : ValueId} {roots : List RootRef}
    (known : ((replacementContentFlow (lower module)).forFunction (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module))).value value = some roots) :
    roots ⊆ (rootsAt ((lowerGlobal module global).init.provenance
      (resultRoots (lower module) (lower module).implTypes)
      ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount).vals value).flatMap
        (lowerGlobal module global).init.expandParameterRoot := by
  obtain ⟨annotations, entries, addresses⟩ := lower_canonical_factory_structure_of_accepted accepted
  exact ReplacementContentFlow.forFunction_value_within_provenance
    (lowerGlobal_canonical_facts_of_accepted accepted globalAt)
    (lower_canonical_facts_of_accepted accepted) annotations entries addresses known

#print axioms lowerContext_factory_value_within_provenance_of_accepted
#print axioms lowerGlobal_factory_value_within_provenance_of_accepted

end Goose.Lower.Validation
