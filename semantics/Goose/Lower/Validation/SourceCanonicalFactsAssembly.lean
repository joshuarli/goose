import Goose.Lower.Validation.AdmittedSourceAccepted
import Goose.Lower.Validation.SourceCanonicalFactsObserved
import Goose.Lower.Validation.SourceCanonicalFactsCalls
import Goose.Lower.Validation.SourceCanonicalFactsRoots
import Goose.Lower.Validation.SourceCanonicalFactsTables
import Goose.Lower.Validation.SourceCanonicalFactsParameters
import Goose.Lower.Validation.SourceCanonicalFactsBounds
import Goose.Lower.Validation.SourceCanonicalFactsCallResults
import Goose.Lower.Validation.SourceCanonicalFactsAcceptedResultFloors
import Goose.Lower.Validation.SourceValueTypeShapesModule
import Goose.Lower.Validation.ProvenanceSourceAccepted
import Goose.Lower.Validation.OperandFunctions
import Goose.Lower.Validation.ReplacementContentFlowSourceFinite
import Goose.GIR.ReplacementContentFlowProofsCanonicalQueries

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

private def nativeResults (module : GIR.Module) : Array (List RootRef) :=
  GIR.resultRoots module module.implTypes

private def nativeProvenance (module : GIR.Module) (func : Func) : Prov :=
  func.provenance (nativeResults module) (func.valueTypes module) module.rootCount

private def nativeProvenances (module : GIR.Module) : Array Prov :=
  module.funcs.map (nativeProvenance module)

private theorem contextCanonicalFacts {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : ContextId} {context : Context} {impl : Core.Impl}
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl) :
    FunctionCanonicalFacts (lower module) (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))
      (nativeProvenance (lower module) (lowerContextAt module context impl)) (nativeResults (lower module)) := by
  have sizes := canonical_provenance_sizes (lowerContextAt module context impl)
    (nativeResults (lower module)) ((lowerContextAt module context impl).valueTypes (lower module))
    (lower module).rootCount
  exact {
    roots := lowerContext_functionRootFacts_of_accepted accepted contextAt implAt
    valuesShape := lowerContext_valueTypeShapes_of_accepted accepted implAt
    globalStorage := lower_canonical_globalStorage_of_accepted accepted _
    fields := lower_canonical_flatFields_of_accepted accepted _
    valuesSize := sizes.1
    slotsSize := sizes.2
    parameters := lowerContext_canonical_parameters_of_accepted accepted implAt
    seeds := lowerContext_canonical_parameter_seeds module context impl _ _ _
    typing := lowerContext_instructionCanonicalFacts_of_accepted accepted contextAt implAt
    uses := (lowerContextAt_operand_bounds module context impl).1
    definitions := lowerContext_canonical_definition_bounds module context impl
    quiet := lowerContextAt_instructionRootsClosed accepted contextAt implAt
    admitted := accepted_context_checkAdmittedRegions accepted contextAt implAt
    loadObserved := lowerContext_canonical_loadObserved_of_accepted accepted contextAt implAt
    calls := lowerContext_canonical_calls_of_accepted accepted contextAt implAt
    callResults := lowerContext_canonical_callResults_of_accepted accepted contextAt implAt }

private theorem globalCanonicalFacts {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : GlobalId} {global : Core.Global}
    (globalAt : module.globals[index]? = some global) :
    FunctionCanonicalFacts (lower module) (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module))
      (nativeProvenance (lower module) (lowerGlobal module global).init) (nativeResults (lower module)) := by
  have sizes := canonical_provenance_sizes (lowerGlobal module global).init
    (nativeResults (lower module)) ((lowerGlobal module global).init.valueTypes (lower module))
    (lower module).rootCount
  exact {
    roots := lowerGlobal_functionRootFacts_of_accepted accepted globalAt
    valuesShape := lowerGlobal_valueTypeShapes_of_accepted accepted globalAt
    globalStorage := lower_canonical_globalStorage_of_accepted accepted _
    fields := lower_canonical_flatFields_of_accepted accepted _
    valuesSize := sizes.1
    slotsSize := sizes.2
    parameters := lowerGlobal_canonical_parameters_of_accepted accepted globalAt
    seeds := lowerGlobal_canonical_parameter_seeds module global _ _ _
    typing := lowerGlobal_instructionCanonicalFacts_of_accepted accepted globalAt
    uses := (lowerGlobal_operand_bounds module global).1
    definitions := lowerGlobal_canonical_definition_bounds module global
    quiet := lowerGlobal_instructionRootsClosed accepted globalAt
    admitted := accepted_global_checkAdmittedRegions accepted globalAt
    loadObserved := by
      intro block blockMember value address load reference parameter member parameterReference
      exact lowerGlobal_canonical_loadObserved module global parameter parameterReference
    calls := lowerGlobal_canonical_calls_of_accepted accepted globalAt
    callResults := lowerGlobal_canonical_callResults_of_accepted accepted globalAt }

private theorem moduleCanonicalFacts {module : Core.Module}
    (accepted : Core.validate module = .ok ()) :
    ModuleCanonicalFacts (lower module) ((lower module).funcs.map (·.valueTypes (lower module)))
      (nativeProvenances (lower module)) (nativeResults (lower module)) := by
  constructor
  · intro index func functionAt
    obtain ⟨context, impl, contextAt, implAt, same⟩ :=
      ReplacementContentFlowSource.accepted_function_context accepted functionAt
    have nativeTypes : (((lower module).funcs.map (·.valueTypes (lower module)))[index]?).getD #[] =
        func.valueTypes (lower module) := by simp [Array.getElem?_map, functionAt]
    have provenance : ((nativeProvenances (lower module))[index]?).getD ⟨#[], #[]⟩ =
        nativeProvenance (lower module) func := by
      simp [nativeProvenances, Array.getElem?_map, functionAt]
    rw [nativeTypes, provenance, same]
    exact contextCanonicalFacts accepted contextAt implAt
  · intro index func functionAt reference
    exact lower_canonical_resultFloor_of_accepted accepted functionAt reference

theorem lower_canonical_factory_structure_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) :
    (∀ (index : FnId) (func : Func), (lower module).funcs[index]? = some func → annotationsValid (lower module) func = true) ∧
    (∀ (index : FnId) (func : Func), (lower module).funcs[index]? = some func →
      ∀ entry : GIR.Block, func.blocks[0]? = some entry → entry.params.length ≤ func.params.length) ∧
    (∀ (index : FnId) (func : Func), (lower module).funcs[index]? = some func → FunctionAddressesBounded (lower module) func) := by
  exact ⟨fun _ _ row => ReplacementContentFlowSource.accepted_function_annotationsValid accepted row,
    fun _ _ row _ entryAt => ReplacementContentFlowSource.accepted_function_entry_length accepted row entryAt,
    fun _ _ row => ReplacementContentFlowSource.accepted_function_addressesBounded accepted row⟩

theorem lowerContext_canonical_facts_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : ContextId} {context : Context} {impl : Core.Impl}
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl) :
    FunctionCanonicalFacts (lower module) (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))
      ((lowerContextAt module context impl).provenance (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount)
      (resultRoots (lower module) (lower module).implTypes) :=
  contextCanonicalFacts accepted contextAt implAt

theorem lowerGlobal_canonical_facts_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : GlobalId} {global : Core.Global}
    (globalAt : module.globals[index]? = some global) :
    FunctionCanonicalFacts (lower module) (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module))
      ((lowerGlobal module global).init.provenance (resultRoots (lower module) (lower module).implTypes)
        ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount)
      (resultRoots (lower module) (lower module).implTypes) :=
  globalCanonicalFacts accepted globalAt

theorem lower_canonical_facts_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) :
    ModuleCanonicalFacts (lower module) ((lower module).funcs.map (·.valueTypes (lower module)))
      ((lower module).funcs.map fun func => func.provenance
        (resultRoots (lower module) (lower module).implTypes)
        (func.valueTypes (lower module)) (lower module).rootCount)
      (resultRoots (lower module) (lower module).implTypes) :=
  moduleCanonicalFacts accepted

theorem lowerContext_factory_owner_local_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : ContextId} {context : Context} {impl : Core.Impl}
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {value : ValueId} {mutability : Mutability} {payload : Ty} {roots : List RootRef} {slot : SlotId}
    (type : ((lowerContextAt module context impl).valueTypes (lower module))[value]? =
      some (some (.data (.ref mutability payload))))
    (owner : payload.ownerElem?.isSome = true)
    (known : (((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))).value value) = some roots)
    (member : RootRef.local slot ∈ roots) :
    ∃ storage, (lowerContextAt module context impl).slots[slot]? = some storage ∧ storage.ty = payload := by
  obtain ⟨annotations, entries, addresses⟩ := lower_canonical_factory_structure_of_accepted accepted
  exact ReplacementContentFlow.forFunction_owner_local
    (lowerContext_canonical_facts_of_accepted accepted contextAt implAt)
    (lower_canonical_facts_of_accepted accepted) annotations entries addresses type owner known member

theorem lowerGlobal_factory_owner_local_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : GlobalId} {global : Core.Global}
    (globalAt : module.globals[index]? = some global)
    {value : ValueId} {mutability : Mutability} {payload : Ty} {roots : List RootRef} {slot : SlotId}
    (type : ((lowerGlobal module global).init.valueTypes (lower module))[value]? =
      some (some (.data (.ref mutability payload))))
    (owner : payload.ownerElem?.isSome = true)
    (known : (((replacementContentFlow (lower module)).forFunction (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module))).value value) = some roots)
    (member : RootRef.local slot ∈ roots) :
    ∃ storage, (lowerGlobal module global).init.slots[slot]? = some storage ∧ storage.ty = payload := by
  obtain ⟨annotations, entries, addresses⟩ := lower_canonical_factory_structure_of_accepted accepted
  exact ReplacementContentFlow.forFunction_owner_local
    (lowerGlobal_canonical_facts_of_accepted accepted globalAt)
    (lower_canonical_facts_of_accepted accepted) annotations entries addresses type owner known member

#print axioms lowerContext_canonical_facts_of_accepted
#print axioms lowerGlobal_canonical_facts_of_accepted
#print axioms lower_canonical_facts_of_accepted
#print axioms lowerContext_factory_owner_local_of_accepted
#print axioms lowerGlobal_factory_owner_local_of_accepted

#print axioms contextCanonicalFacts
#print axioms globalCanonicalFacts
#print axioms moduleCanonicalFacts
#print axioms lower_canonical_factory_structure_of_accepted

end Goose.Lower.Validation
