import Goose.Lower.Validation.SourceReplacementCallContentsApartLocal

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR Goose.Core.Sound SummaryPreservation ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

def RhsInactiveSliceHolder (implementation : Impl) (rhs : Expr) (active : List VarId) (slot : Nat) : Prop :=
  ∃ localVar, implementation.vars[slot]? = some localVar ∧ localVar.ty.isSlice = true ∧
    slot ∈ rhs.variables ∧ slot ∉ active

theorem site_call_contents_apart_of_scoped_memory {module : Core.Module}
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
    {callee : Context} {calleeImpl : Impl} {declared : List RootRef}
    (calleeAt : module.contexts[function]? = some callee)
    (calleeImplAt : module.impls[callee.impl]? = some calleeImpl)
    (occurrence : CallOccurrence site.localEnv (.expression site.source.site.source.rhs)
      (lowerContextAt module context implementation) upper value function arguments callOrigin)
    (annotation : (lowerContextAt module callee calleeImpl).roots.contents.find? (·.1 == index) = some (index, declared))
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
  obtain ⟨localEnv, path, syntaxArgs, sourceOrigin, ceiling, actual, access, source,
    trace, physical, known, within, receiver⟩ := site_call_content_receiver_bound_of_accepted
      accepted contextAt implementationAt site below finalAt member called calleeAt calleeImplAt
      occurrence annotation argumentAt
  have accessEq : localEnv.access = demand.planContext.approvals.access := by
    rw [demand.access_context contextAt implementationAt]
    exact access.trans site.access
  have implementationEq : localEnv.impl = implementation := congrArg AccessEnv.impl (access.trans site.access)
  have contextEq : localEnv.ctx = context := congrArg AccessEnv.ctx (access.trans site.access)
  obtain ⟨target, targetAt, ownerKnown⟩ :=
    site_owner_query_of_accepted accepted contextAt implementationAt site demand below
  have invalidates := site_owner_invalidates contextAt implementationAt site demand targetAt
  have closed := lowerContextAt_parameterRoots_closed accepted contextAt implementationAt
  rcases receiver with ⟨mutability, slot, syntaxAt, localAnnotation⟩ |
    ⟨mutability, parameter, syntaxAt, localContents⟩
  · have used : slot ∈ site.source.site.source.rhs.variables :=
      call_argument_variable_in_rhs source syntaxAt (by simp [Arg.variables, Place.variables])
    have reference := (lowerContext_canonical_facts_of_accepted accepted calleeAt calleeImplAt).roots.contentTypes
      index declared annotation
    obtain ⟨localVar, variableAt, slice⟩ := CallArgumentsTrace.local_slice_type trace accepted
      ((congrArg AccessEnv.mod access).trans (congrArg AccessEnv.mod site.access))
      calleeAt calleeImplAt reference syntaxAt
    by_cases active : slot ∈ demand.statement.expected.frame.active
    · apply content_atomsWithin_of_extends growth (growth.values.values argument)
      · exact demand.rhs_active_local_content_atoms_apart accessEq variableAt slice localAnnotation
          used active targetAt invalidates closed ownerKnown known within
      · exact normalize_nonpending known
    · have native := lowerContext_canonical_facts_of_accepted accepted contextAt implementationAt
      obtain ⟨annotations, entries, addresses⟩ := lower_canonical_factory_structure_of_accepted accepted
      have canonical := ReplacementContentFlow.forFunction_canonicalWithin native
        (lower_canonical_facts_of_accepted accepted) annotations entries addresses finalAt
      apply canonical_call_local_content_atoms native canonical member called (lower_func_at calleeAt calleeImplAt)
        reference argumentAt (CallArgumentsPhysical.local_roots physical argumentAt syntaxAt) (below.vals argument) growth
      exact memory.slots slot ⟨localVar, by simpa only [implementationEq] using variableAt, slice, used, active⟩
  · have used : parameter ∈ site.source.site.source.rhs.variables :=
      call_argument_variable_in_rhs source syntaxAt (by simp [Arg.variables, Place.variables, Expr.variables])
    have contentsAt : (context.contentRoots.find? (·.1 == parameter)).map (·.2) = some ceiling := by
      simpa only [PEnv.cont, contextEq] using localContents
    apply content_atomsWithin_of_extends growth (growth.values.values argument)
    · exact demand.rhs_forwarded_content_atoms_apart accepted contextAt implementationAt contentsAt
        used targetAt invalidates closed ownerKnown known within
    · exact normalize_nonpending known

#print axioms site_call_contents_apart_of_scoped_memory

end Goose.Lower.Validation
