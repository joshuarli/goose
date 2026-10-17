import Goose.Lower.Validation.ReplacementCallSummaryApart
import Goose.Lower.Validation.ReplacementOwnerDependencyApart

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR Goose.Core.Sound SummaryPreservation

theorem ReplacementDemandContext.known_call_summary_apart_of_accepted {module : Core.Module}
    {planOwner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (demand : ReplacementDemandContext module planOwner path place rhs origin)
    (accepted : Core.validate module = .ok ())
    (accessModule : demand.planContext.approvals.access.mod = module)
    {suffix : List Nat} {function : ContextId} {syntaxArgs : List Arg} {callOrigin : OriginId}
    (source : DemandNodeAt (.expression rhs) suffix (.expression (.call function syntaxArgs callOrigin)))
    {context : Context} {impl : Impl} {summary : Core.Summary}
    (contextAt : module.contexts[function]? = some context)
    (implAt : module.impls[context.impl]? = some impl) (summaryAt : impl.summary = .known summary)
    {func : Func} {queries : ReplacementQueries} {owner : ValueId} {arguments : List ValueId}
    {target : DemandOwner} (targetAt : demand.planContext.approvals.access.owner place = .ok target)
    (closed : ParameterRootsClosed func)
    (ownerKnown : ReplacementRootsWithin (queries.value owner) (target.roots.flatMap func.expandParameterRoot))
    (argumentsAt : ∀ index, index < impl.params.size → ∃ argument, arguments[index]? = some argument)
    (argumentApart : ∀ argument ∈ arguments, ReplacementApart queries owner (queries.ownerDependencies argument)) :
    ReplacementApart queries owner (callSummaryRoots (lower module) queries function arguments) := by
  obtain ⟨_, effects, _, effectsAt, _⟩ := demand.descendant_call_disjoint source
  have contextLookup : demand.planContext.approvals.access.mod.contexts[function]? = some context :=
    by simpa only [accessModule] using contextAt
  have implLookup : demand.planContext.approvals.access.mod.impls[context.impl]? = some impl :=
    by simpa only [accessModule] using implAt
  have effectGlobal : ∀ global, RootRef.global global ∈ effects.flatMap DemandOwner.roots →
      ReplacementApart queries owner (some [RootRef.global global]) := by
    intro global member
    simpa only [Func.expandParameterRoot] using
      demand.call_effect_owner_root_apart source targetAt effectsAt closed ownerKnown member
  apply callSummaryRoots_known_apart (lower_func_at contextAt implAt) summaryAt argumentApart
  · intro global member
    exact effectGlobal global (callEffectOwners_known_global contextLookup implLookup summaryAt effectsAt member)
  · intro index member
    have bound := validate_summaryTarget_bounds accepted implAt summaryAt (.param index) member
    refine ⟨argumentsAt index bound, ?_⟩
    let parameter := impl.params[index]'bound
    have parameterAt : impl.params[index]? = some parameter := Array.getElem?_eq_getElem bound
    have annotationEq := lowerContext_parameterGlobalRoots_of_accepted accepted contextAt implAt parameterAt
    let globalRoots := (paramGlobals impl context index).filterMap
      (fun | .global global => some (RootRef.global global) | _ => none)
    have singletons : ∀ row ∈ globalRoots.map (fun root => [root]),
        ReplacementApart queries owner (some row) := by
      intro row rowMember
      obtain ⟨root, rootMember, same⟩ := List.mem_map.mp rowMember
      subst row
      obtain ⟨target, targetMember, mapped⟩ := List.mem_filterMap.mp rootMember
      cases target with
      | param i => simp at mapped
      | global global =>
        have rootEq : RootRef.global global = root := Option.some.inj mapped
        subst root
        exact effectGlobal global
          (callEffectOwners_known_parameter_global contextLookup implLookup summaryAt effectsAt member targetMember)
    have apart := ReplacementApart.flatten singletons
    have rootsApart : ReplacementApart queries owner (some globalRoots) := by
      change ReplacementApart queries owner (some (globalRoots.flatMap (fun root => [root]))) at apart
      simpa using apart
    have transported := (congrArg (fun roots => ReplacementApart queries owner (some roots)) annotationEq).mpr rootsApart
    apply Eq.mp _ transported
    congr 3

theorem ReplacementDemandContext.call_summary_global_atom_apart {module : Core.Module}
    {planOwner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (demand : ReplacementDemandContext module planOwner path place rhs origin)
    (accepted : Core.validate module = .ok ())
    (accessModule : demand.planContext.approvals.access.mod = module)
    {suffix : List Nat} {function : ContextId} {syntaxArgs : List Arg} {callOrigin : OriginId}
    (source : DemandNodeAt (.expression rhs) suffix (.expression (.call function syntaxArgs callOrigin)))
    {context : Context} {impl : Impl} {summary : Core.Summary}
    (contextAt : module.contexts[function]? = some context)
    (implAt : module.impls[context.impl]? = some impl) (summaryAt : impl.summary = .known summary)
    {func : Func} {queries : ReplacementQueries} {owner : ValueId}
    {target : DemandOwner} (targetAt : demand.planContext.approvals.access.owner place = .ok target)
    (closed : ParameterRootsClosed func)
    (ownerKnown : ReplacementRootsWithin (queries.value owner) (target.roots.flatMap func.expandParameterRoot))
    {global : GlobalId}
    (expanded : Target.global global ∈ (lowerContextAt module context impl).storageTargets
      (summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks ++ summary.rebinds)) :
    OwnerDependencyApart (lower module) func queries owner (.global global) := by
  obtain ⟨_, effects, _, effectsAt, _⟩ := demand.descendant_call_disjoint source
  have contextLookup : demand.planContext.approvals.access.mod.contexts[function]? = some context := by
    simpa only [accessModule] using contextAt
  have implLookup : demand.planContext.approvals.access.mod.impls[context.impl]? = some impl := by
    simpa only [accessModule] using implAt
  rw [lowerContextAt_storageTargets_eq accepted contextAt implAt
    (fun target member => validate_summaryTarget_bounds accepted implAt summaryAt target member)] at expanded
  have actualMember := callEffectOwners_known_expanded_global contextLookup implLookup summaryAt effectsAt expanded
  have apart : ReplacementApart queries owner (some [RootRef.global global]) := by
    simpa only [Func.expandParameterRoot] using
      demand.call_effect_owner_root_apart source targetAt effectsAt closed ownerKnown actualMember
  refine ⟨ReplacementContentFlow.Model.ownerTouches (lower module) [.global global],
    ReplacementContentFlow.Model.ownerDependencies_literal_global _ _ _, ?_⟩
  exact apart.of_subset rfl (ReplacementContentFlow.Model.ownerTouches_subset _ _)

#print axioms ReplacementDemandContext.known_call_summary_apart_of_accepted
#print axioms ReplacementDemandContext.call_summary_global_atom_apart

end Goose.Lower.Validation
