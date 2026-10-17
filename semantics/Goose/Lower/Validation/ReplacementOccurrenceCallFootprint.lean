import Goose.Lower.Validation.ReplacementCallFootprintSubstitution
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceLedger

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR Goose.Core.Sound SummaryPreservation ReplacementContentFlow.Model

theorem CallOccurrence.substitute_footprint_apart {module : Core.Module}
    {planOwner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (demand : ReplacementDemandContext module planOwner path place rhs origin)
    (accepted : Core.validate module = .ok ())
    {env : PEnv} (environment : env.mod = module)
    (access : env.access = demand.planContext.approvals.access)
    {func callee : Func} {types : Array (Option VTy)} {provenance upper : Prov} {results : Array (List RootRef)}
    (native : FunctionCanonicalFacts (lower module) func types provenance results)
    {queries : ReplacementQueries} {owner value function : ValueId} {arguments : List ValueId}
    {callOrigin : Option OriginId} {block : GIR.Block}
    (member : block ∈ func.blocks.toList)
    (called : Inst.def value (.call function arguments callOrigin) ∈ block.insts)
    (calleeAt : (lower module).funcs[function]? = some callee)
    (occurrence : CallOccurrence env (.expression rhs) func upper value function arguments callOrigin)
    {target : DemandOwner} (targetAt : demand.planContext.approvals.access.owner place = .ok target)
    (closed : ParameterRootsClosed func)
    (ownerKnown : ReplacementRootsWithin (queries.value owner) (target.roots.flatMap func.expandParameterRoot))
    {current : State} {raw : Roots}
    (footprint : raw.AtomsWithin (TouchFootprintAtom callee (summaryTouchPolicy (lower module) callee)))
    (supported : raw.Supported (atomUniverse (lower module) callee))
    (normalizable : raw.AtomsWithin (fun atom => (normalizeAtom callee atom).isSome = true))
    (external : raw.AtomsWithin (fun atom => ∀ slot, atom ≠ .local slot))
    (argumentAtoms : ∀ argument ∈ arguments,
      (flowAt current.values argument).AtomsWithin (OwnerDependencyApart (lower module) func queries owner))
    (contents : ∀ (index : Nat), (callee.roots.contents.find? (·.1 == index)).isSome = true →
      (callee.params[index]?).any Ty.isRefSlice = true →
      ∀ (argument : ValueId), arguments[index]? = some argument →
      (content func current (flowAt current.values argument)).AtomsWithin
        (OwnerDependencyApart (lower module) func queries owner)) :
    (substitute func current arguments raw).AtomsWithin
      (OwnerDependencyApart (lower module) func queries owner) := by
  obtain ⟨localEnv, sourcePath, syntaxArgs, sourceOrigin, before, sourceRoots, argumentsAfter,
    returned, after, localAccess, _, source, replayed, contentsChecked, callReplayed, _, _, argumentOrigins, _, trace⟩ := occurrence
  have moduleEq : localEnv.mod = module := (congrArg AccessEnv.mod localAccess).trans environment
  obtain ⟨context, impl, contextAt, implAt, _, _, _⟩ :=
    rpCall_ok localEnv function sourceRoots argumentsAfter returned after callReplayed
  have contextRow : module.contexts[function]? = some context := by simpa only [moduleEq] using contextAt
  have implRow : module.impls[context.impl]? = some impl := by simpa only [moduleEq] using implAt
  have loweredAt := lower_func_at contextRow implRow
  have calleeEq : callee = lowerContextAt module context impl := Option.some.inj (calleeAt.symm.trans loweredAt)
  subst callee
  obtain ⟨callSite⟩ := native.calls block member value function arguments callOrigin called
  have same : callSite.callee = lowerContextAt module context impl :=
    Option.some.inj (callSite.calleeAt.symm.trans loweredAt)
  have accessModule : demand.planContext.approvals.access.mod = module :=
    (congrArg AccessEnv.mod access).symm.trans environment
  have calleeFacts := (lower_canonical_facts_of_accepted accepted).functions function _ loweredAt
  apply substitute_touch_footprint_apart footprint supported normalizable external calleeFacts.roots ?_ ?_ ?_ contents
  · intro index bound
    obtain ⟨argument, argumentAt, _⟩ := callSite.arguments index (same ▸ bound)
    exact ⟨argument, argumentAt⟩
  · intro global bound policy
    exact demand.call_footprint_global_apart accepted accessModule source contextRow implRow targetAt closed ownerKnown
      (by simpa only [lower, Array.size_map] using bound) policy
  · intro index bound argument row
    exact argumentAtoms argument (List.mem_of_getElem? row)

#print axioms CallOccurrence.substitute_footprint_apart

end Goose.Lower.Validation.ReplacementContentFlowSource
