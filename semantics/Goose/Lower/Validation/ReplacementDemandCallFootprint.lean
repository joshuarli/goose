import Goose.Lower.Validation.SourceTouchFootprintAccepted
import Goose.Lower.Validation.ReplacementDemandCallSummary
import Goose.Lower.Validation.SourceReadyCertificate

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR Goose.Core.Sound SummaryPreservation ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem ReplacementDemandContext.call_footprint_global_apart {module : Core.Module}
    {planOwner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (demand : ReplacementDemandContext module planOwner path place rhs origin)
    (accepted : Core.validate module = .ok ())
    (accessModule : demand.planContext.approvals.access.mod = module)
    {suffix : List Nat} {function : ContextId} {syntaxArgs : List Arg} {callOrigin : OriginId}
    (source : DemandNodeAt (.expression rhs) suffix (.expression (.call function syntaxArgs callOrigin)))
    {context : Context} {impl : Impl}
    (contextAt : module.contexts[function]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {func : Func} {queries : ReplacementQueries} {owner : ValueId}
    {target : DemandOwner} (targetAt : demand.planContext.approvals.access.owner place = .ok target)
    (closed : ParameterRootsClosed func)
    (ownerKnown : ReplacementRootsWithin (queries.value owner) (target.roots.flatMap func.expandParameterRoot))
    {global : GlobalId} (bounded : global < module.globals.size)
    (policy : summaryTouchPolicy (lower module) (lowerContextAt module context impl) (.global global)) :
    OwnerDependencyApart (lower module) func queries owner (.global global) := by
  let declaration := module.globals[global]'bounded
  have globalAt : module.globals[global]? = some declaration := Array.getElem?_eq_getElem bounded
  have nativeGlobalAt : (lower module).globals[global]? = some (lowerGlobal module declaration) := by
    simp only [lower, Array.getElem?_map, globalAt, Option.map_some]
  have rawGlobal (caller : Func) : ownerDependencies (lower module) caller (.known [.global global]) =
      some (if declaration.ty.ownerElem?.isSome then [.global global] else []) := by
    rw [ownerDependencies_literal_global]
    simp [ownerTouches, accepted_storageClosed accepted, List.filter_cons, nativeGlobalAt, lowerGlobal]
  by_cases owning : declaration.ty.ownerElem?.isSome = true
  · cases summaryAt : impl.summary with
    | unknown =>
      obtain ⟨_, effects, _, effectsAt, _⟩ := demand.descendant_call_disjoint source
      have contextLookup : demand.planContext.approvals.access.mod.contexts[function]? = some context := by
        simpa only [accessModule] using contextAt
      have implLookup : demand.planContext.approvals.access.mod.impls[context.impl]? = some impl := by
        simpa only [accessModule] using implAt
      have sourceGlobalAt : demand.planContext.approvals.access.mod.globals[global]? = some declaration := by
        simpa only [accessModule] using globalAt
      have rootAt := callEffectOwners_unknown_global contextLookup implLookup summaryAt effectsAt sourceGlobalAt owning
      have apart : ReplacementApart queries owner (some [RootRef.global global]) := by
        simpa only [Func.expandParameterRoot] using
          demand.call_effect_owner_root_apart source targetAt effectsAt closed ownerKnown rootAt
      exact ⟨[.global global], by simpa only [owning, ↓reduceIte] using rawGlobal func, apart⟩
    | known summary =>
      have loweredSummary : (lowerContextAt module context impl).summary = .known summary := summaryAt
      simp only [summaryTouchPolicy, summaryTouchRoots, loweredSummary] at policy
      obtain ⟨actual, actualAt, bound⟩ := policy
      have same : actual = [.global global] := Option.some.inj
        (actualAt.symm.trans (by simpa only [owning, ↓reduceIte] using rawGlobal (lowerContextAt module context impl)))
      subst actual
      rcases bound (.global global) (by simp) with ⟨slot, impossible⟩ | globalBound
      · cases impossible
      · obtain ⟨target, targetMember, mapped⟩ := List.mem_map.mp globalBound
        have expanded : Target.global global ∈ (lowerContextAt module context impl).storageTargets
            (summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks ++ summary.rebinds) := by
          have targetEq : target = .global global := by cases target <;> simp_all
          subst target
          exact storageTargets_mono (fun target member => List.mem_append_left _ member)
            _ targetMember
        exact demand.call_summary_global_atom_apart accepted accessModule source contextAt implAt summaryAt
          targetAt closed ownerKnown expanded
  · exact ⟨[], by simpa [owning] using rawGlobal func, Or.inl rfl⟩

#print axioms ReplacementDemandContext.call_footprint_global_apart

end Goose.Lower.Validation
