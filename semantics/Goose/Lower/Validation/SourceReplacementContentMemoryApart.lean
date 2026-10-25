import Goose.Lower.Validation.SourceReplacementCallContentsApartMemory
import Goose.Lower.Validation.SourceReplacementContentCallsApart

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem site_native_call_contents_apart_of_scoped_memory {module : Core.Module}
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
    {block : GIR.Block} (member : block ∈ (lowerContextAt module context implementation).blocks.toList)
    {value function index argument : Nat} {arguments : List ValueId} {callOrigin : Option OriginId}
    (called : Inst.def value (.call function arguments callOrigin) ∈ block.insts)
    {callee : Func} (calleeAt : (lower module).funcs[function]? = some callee)
    (observed : (callee.roots.contents.find? (·.1 == index)).isSome = true)
    (occurrence : CallOccurrence site.localEnv (.expression site.source.site.source.rhs)
      (lowerContextAt module context implementation) upper value function arguments callOrigin)
    (argumentAt : arguments[index]? = some argument)
    (growth : current.Extends final)
    (memory : current.ScopedMemoryWithin
      (RhsInactiveSliceHolder implementation site.source.site.source.rhs
        demand.statement.expected.frame.active) (fun _ => False)
      (OwnerDependencyApart (lower module) (lowerContextAt module context implementation)
        (replacementQueries (lower module) (lowerContextAt module context implementation)
          ((lowerContextAt module context implementation).valueTypes (lower module))) owner)) :
    (content (lowerContextAt module context implementation) current (flowAt current.values argument)).AtomsWithin
      (OwnerDependencyApart (lower module) (lowerContextAt module context implementation)
        (replacementQueries (lower module) (lowerContextAt module context implementation)
          ((lowerContextAt module context implementation).valueTypes (lower module))) owner) := by
  obtain ⟨sourceCallee, calleeImpl, sourceAt, implAt, same⟩ := accepted_function_context accepted calleeAt
  subst callee
  cases annotation : (lowerContextAt module sourceCallee calleeImpl).roots.contents.find? (·.1 == index) with
  | none => simp [annotation] at observed
  | some row =>
    have found := annotation
    rw [← Array.find?_toList] at found
    have selected : row.1 = index := by simpa using List.find?_some found
    obtain ⟨first, declared⟩ := row
    dsimp only at selected
    subst first
    exact site_call_contents_apart_of_scoped_memory accepted contextAt implementationAt site demand below
      finalAt member called sourceAt implAt occurrence annotation argumentAt growth memory

theorem site_rhs_apart_of_final_scoped_memory {module : Core.Module}
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
    {final : State}
    (finalModel : ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))).model = some final)
    (within : final.ScopedContentWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs)
      (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper
      site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size)
      (RhsInactiveSliceHolder impl site.source.site.source.rhs demand.statement.expected.frame.active)
      (fun _ => False)
      (OwnerDependencyApart (lower module) (lowerContextAt module context impl)
        (replacementQueries (lower module) (lowerContextAt module context impl)
          ((lowerContextAt module context impl).valueTypes (lower module))) owner))
 :
    EmitsOnly (ReplacementInstApart (lower module) ((lowerContextAt module context impl).valueTypes (lower module))
      (replacementQueries (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module))) owner)
      site.source.site.source.site.cleared site.source.site.source.site.captured := by
  apply site_rhs_apart_of_final_content accepted contextAt implAt site demand below finalModel within.values
  intro value block function arguments callOrigin member called occurrence callee calleeAt index observed reference argument argumentAt
  exact site_native_call_contents_apart_of_scoped_memory accepted contextAt implAt site demand below finalModel
    member called calleeAt observed occurrence argumentAt (.refl final) within.memory

#print axioms site_native_call_contents_apart_of_scoped_memory
#print axioms site_rhs_apart_of_final_scoped_memory

end Goose.Lower.Validation
